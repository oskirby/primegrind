#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <getopt.h>
#include <sys/time.h>
#include <pthread.h>

#define PRIME_MAX               10000

#define PRIME_WORD_BITS         (sizeof(unsigned long) * 8)
#define PRIME_WORD_DENSITY      (PRIME_WORD_BITS * 2)
#define PRIME_MEM_WORDS(_p_)    (((_p_) + PRIME_WORD_DENSITY - 1) / PRIME_WORD_DENSITY)

/* Flip a bit corresponding to a potential prime, p */
static inline void
flip(unsigned long long p, unsigned long long offset, unsigned long *mem)
{
    if (!(p & 1)) return;
    if (p <= offset) return;
    p = (p-offset-1)/2;
    __atomic_fetch_xor(&mem[p / PRIME_WORD_BITS], (1UL << (p % PRIME_WORD_BITS)), __ATOMIC_ACQUIRE);
}

static inline void
clear(unsigned long long p, unsigned long long offset, unsigned long *mem)
{
    if (!(p & 1)) return;
    if (p <= offset) return;
    p = (p-offset-1)/2;
    __atomic_fetch_and(&mem[p / PRIME_WORD_BITS], ~(1UL << (p % PRIME_WORD_BITS)), __ATOMIC_ACQUIRE);
}

static inline int
test(unsigned long long p, unsigned long long offset, const unsigned long *mem)
{
    if (!(p & 1)) return 0;
    if (p <= offset) return 0;
    p = (p-offset-1)/2;
    return (mem[p / PRIME_WORD_BITS] >> (p % PRIME_WORD_BITS)) & 1;
}

/* Integer square root. */
static unsigned long
isqrt(unsigned long long x)
{
    unsigned long small, large;
    if (x < 2) {
        return 1;
    }
    small = isqrt(x >> 2) << 1;
    large = small+1;
    return ((large*large) > x) ? small : large;
}

/* Return the square root mod 12, or zero for a quadratic non-residue. */
static unsigned int
sqrt_mod12(int x)
{
    if (x < 0) x += 12;
    switch (x) {
        case 1:
            return 1;
        case 4:
            return 2;
        case 9:
            return 3;
        default:
            return 0;
    }
}

static void
atkin_skiptab(unsigned int *tab)
{
    unsigned int i, n;
    for (i = 0; i < 12; i++) {
        for (n = 1; n < 12; n++) {
            unsigned int modulo = ((2*i + n) * n) % 12;
            if (!modulo) break;
        }
        tab[i] = n;
    }
}

struct worker_data {
    pthread_mutex_t     mutex;
    unsigned int        workers;    /* Number of worker threads to use. */
    unsigned long long  offset;     /* The minimum prime to start at. */
    unsigned long long  pmax;       /* The maximum prime desired */
    unsigned long       psqrt;      /* sqrt(pmax) */
    unsigned long long  p;
    unsigned long long  x;
    unsigned long       *mem;       /* Destination memory for prime data. */
    unsigned long       *lowprimes; /* Table of precomputed low primes. */
};

/* Inner loop of the Sieve of Aktin, computes all potentially prime solutions
 * of the set of Diophantine equations:
 *      4*x^2 + y^2 == p for p == 1 mod 4
 *      3*x^2 + y^2 == p for p == 7 mod 12
 *      3*x^2 - y^2 == p for p == 11 mod 12
 *
 * And flips the 'possibly prime' bit corresponding to the prime. A number in
 * that remains in this set will either be prime, or will contain a square of a
 * prime in its factorization.
 */
static void
atkin_inner(struct worker_data *data, unsigned long x)
{
    /* Some precompute acceleration */
    unsigned long long x2 = (unsigned long long)x*x;
    unsigned int residue;
    unsigned int xmod = 3*x2 % 12;
    unsigned long y;

    /*
     * For any given y^2 == r mod 12, we can solve
     *      (y+n)^2 == r mod 12, as
     *      2y*n + n^2 == 0 mod 12.
     *
     * This gives us the spacing between adjacent squares with
     * the same remainder mod 12 for a given value of y. The
     * solutions to this equation are used as a lookup table
     * for the inner loops.
     */
    unsigned int skiptab[12] = {
        6, 4, 2, 6, 4, 2, 6, 4, 2, 6, 4, 2
    };

    /* Test for primes satisfying p = 4*x*x + y*y when p == 1 mod 4 */
    /* Since 4*x^2 == 0 mod 4, we are interested in solutions to
     * y^2 == 1 mod 4, which is true for all odd values of y.
     */
    for (y = 1;; y += 2) {
        unsigned long long p = 4*x2 + y*y;
        if (p >= data->pmax) break;
        flip(p, data->offset, data->mem);
    }

    /* Test for primes satisfying p = 3*x*x + y*y when p == 7 mod 12 */
    /*
     * Shuffle some things around to get y*y == (7 - 3*x*x) mod 12, which
     * will only have integer solutions when (7 - 3*x*x) mod 12 is a
     * quadratic residue.
     */
    residue = (xmod > 7) ? (19 - xmod) : (7 - xmod);
    y = sqrt_mod12(residue);
    if (y) {
        /*
         * Note the periodicity in skiptab used to speed up the inner loop,
         * there is probably an explaination for this that has to do with
         * the residues of 2y*n + n^2 == 0 mod 12.
         */
        unsigned int skip =  6 - (y % 3)*2;
        while (1) {
            unsigned long long p = 3*x2 + y*y;
            if (p >= data->pmax) break;
            flip(p, data->offset, data->mem);
            y += skip;
            if (skip != 6) skip = 6 - skip;
        }
    }

    /* Test for primes satisfying p = 3*x*x - y*y when p == 11 mod 12 and x>y */
    /*
     * Shuffle some things around to get y*y == (3*x*x - 11) mod 12, which
     * will only have integer solutions when (3*x*x - 11) mod 12 is a
     * quadratic residue.
     */
    residue = (xmod + 1);
    y = sqrt_mod12(residue);
    if (y) {
        unsigned int skip =  6 - (y % 3)*2;
        while (y < x) {
            unsigned long long p = 3*x2 - y*y;
            if (p < data->pmax) flip(p, data->offset, data->mem);
            y += skip;
            if (skip != 6) skip = 6 - skip;
        }
    }
}

static void
atkin_clear_squares(struct worker_data *data, unsigned long p)
{
    unsigned long long psquare = (unsigned long long)p * p;
    unsigned long long i = psquare;
    if (i < data->offset) {
        i = data->offset + psquare - (data->offset % psquare);
    }
    while (i < data->pmax) {
        clear(i, data->offset, data->mem);
        i += psquare;
    }
}

/* For a multithreaded version. */
static void *
atkin_worker(void *arg)
{
    struct worker_data *data = arg;

    /* Eliminate squarefree composite numbers. */
    do {
        unsigned long long x = __atomic_fetch_add(&data->x, 1, __ATOMIC_ACQUIRE);
        if (x >= data->psqrt) break;
        atkin_inner(data, x);
    } while(1);

    /* Eliminate the squares of primes. */
    do {
        unsigned long long p = __atomic_fetch_add(&data->p, PRIME_WORD_DENSITY, __ATOMIC_ACQUIRE);
        int i;
        if (p >= data->psqrt) break;
        for (i = 0; i < PRIME_WORD_DENSITY; i += 2) {
            if (test(p+i, 0, data->lowprimes)) {
                atkin_clear_squares(data, p+i);
            }
        }
    } while (1);
}

/* The Sieve of Atkin */
static void
atkin_sieve(struct worker_data *data)
{
    /* Set all numbers as composite */
    memset(data->mem, 0, sizeof(unsigned long) * PRIME_MEM_WORDS(data->pmax - data->offset));
    if (!data->offset) flip(3, 0, data->mem);
    data->p = 3;
    data->x = 0;

    if (!data->offset) {
        data->lowprimes = data->mem;
    }

    /* Go Parallel */
    if (data->workers > 1) {
        pthread_t worker_threads[data->workers];
        unsigned int i;

        /* Launch workers and wait for them to finish. */
        for (i = 0; i < data->workers; i++) {
            pthread_create(&worker_threads[i], NULL, atkin_worker, data);
        }
        for (i = 0; i < data->workers; i++) {
            pthread_join(worker_threads[i], NULL);
        }
    }
    /* Single-threaded */
    else {
        atkin_worker(data);
    }
    clear(1, 0, data->mem);
}

static void
eratosthenes_clear_multiples(struct worker_data *data, unsigned long long p)
{
    unsigned long long i = p+p;
    if (i < data->offset) {
        i = data->offset + p - (data->offset % p);
    }
    while (i < data->pmax) {
        clear(i, data->offset, data->mem);
        i += p;
    }
}

static void *
eratosthenes_worker(void *arg)
{
    struct worker_data *data = arg;
    do {
        unsigned long long p = __atomic_fetch_add(&data->p, PRIME_WORD_DENSITY, __ATOMIC_ACQUIRE);
        int i;
        if (p >= data->psqrt) break;
        for (i = 0; i < PRIME_WORD_DENSITY; i += 2) {
            if (test(p+i, 0, data->lowprimes)) {
                eratosthenes_clear_multiples(data, p+i);
            }
        }
    } while (1);
}

/* The Sieve of Eratosthenes */
static void
eratosthenes_sieve(struct worker_data *data)
{
    /* Set all numbers as prime */
    memset(data->mem, ~0, sizeof(unsigned long) * PRIME_MEM_WORDS(data->pmax - data->offset));
    if (!data->offset) clear(1, 0, data->mem);
    data->p = 3;
    data->x = data->offset;

    /* Windowed version - requires a precomputed lowprime table. */
    if (data->offset && !data->lowprimes) {
        struct worker_data precompute = {
            .mutex = PTHREAD_MUTEX_INITIALIZER,
            .workers = 1,
            .offset = 0,
            .pmax = data->psqrt,
            .psqrt = isqrt(data->psqrt),
        };
        precompute.mem = malloc(PRIME_MEM_WORDS(data->psqrt) * sizeof(unsigned long));
        if (!precompute.mem) {
            fprintf(stderr, "Memory allocation failed: %s\n", strerror(errno));
            exit(EXIT_FAILURE);
        }
        eratosthenes_sieve(&precompute);
        data->lowprimes = precompute.mem;
    }
    /* Otherwise, precompute enough prime numbers to give each worker one block. */
    else if (!data->lowprimes) {
        unsigned long lowprimes[data->workers];
        struct worker_data precompute = {
            .mutex = PTHREAD_MUTEX_INITIALIZER,
            .workers = 1,
            .offset = 0,
            .pmax = PRIME_WORD_DENSITY * data->workers,
            .psqrt = isqrt(PRIME_WORD_DENSITY * data->workers),
            .mem = data->mem,
            .lowprimes = data->mem,
        };
        eratosthenes_sieve(&precompute);
        data->lowprimes = data->mem;
    }

    /* Multithreaded version. */
    if (data->workers > 1) {
        pthread_t worker_threads[data->workers];
        unsigned int i;
        /* Launch workers and wait for them to finish. */
        for (i = 0; i < data->workers; i++) {
            pthread_create(&worker_threads[i], NULL, eratosthenes_worker, data);
        }
        for (i = 0; i < data->workers; i++) {
            pthread_join(worker_threads[i], NULL);
        }
    }
    /* Single-threaded version */
    else {
        eratosthenes_worker(data);
    }
}

static void
usage(int argc, char * const argv[])
{
    fprintf(stdout, "Usage: %s [options] [PMAX]\n\n", argv[0]);
    fprintf(stdout, "Search for prime numbers less than PMAX\n\n");
    fprintf(stdout, "options:\n");
    fprintf(stdout, "\t-a       use the Sieve of Aktin algorithm\n");
    fprintf(stdout, "\t-e       use the Sieve of Eratosthenes algorithm\n");
    fprintf(stdout, "\t-s PMIN  search for prime numbers starting from PMIN\n");
    fprintf(stdout, "\t-j NUM   distribute work amongst NUM threads");
    fprintf(stdout, "\t-r       output raw binary bitmask of even primes\n");
    fprintf(stdout, "\t-q       do not output primes, just perform timing\n");
    fprintf(stdout, "\t-h       display this message and exit\n");
}

#define OUTPUT_QUIET    0
#define OUTPUT_DECIMAL  1
#define OUTPUT_RAW      2

/* Parse a big integer, with an optional suffix, or blow up and exit on failure. */
static unsigned long long
parse_bigint(const char *str, const char *meta)
{
    char *e;
    unsigned long long x = strtoull(str, &e, 0);
    /* Check for a suffix */
    if (*e == '\0') {
        return x;
    }
    /* Binary suffixes */
    if ((e[1] == 'i') && (e[2] == '\0')) {
        switch (e[0]) {
            case 'k':
                return x << 10;
            case 'M':
                return x << 20;
            case 'G':
                return x << 30;
            case 'T':
                return x << 40;
            default:
                break;
        }
    }
    /* SI suffixes */
    else if (e[1] == '\0') {
        switch (e[0]) {
            case 'k':
                return x * 1000ULL;
            case 'M':
                return x * 1000000ULL;
            case 'G':
                return x * 1000000000ULL;
            case 'T':
                return x * 1000000000000ULL;
            default:
                break;
        }
    }
    /* Should only get here if there was a parsing error. */
    fprintf(stderr, "Invalid value of %s: \'%s\'\n", meta, str);
    exit(EXIT_FAILURE);
}

int
main(int argc, char * const argv[])
{
    struct timespec start, end;

    unsigned long long msec;
    void (*algo)(struct worker_data *) = atkin_sieve;
    const char *shortopts = "aerqs:j:h";
    unsigned int output_type = OUTPUT_DECIMAL;
    struct worker_data data = {
        .mutex = PTHREAD_MUTEX_INITIALIZER,
        .workers = 1,
        .offset = 0,
        .pmax = 1000000
    };

    int c;
    optind = 1;
    while ((c = getopt(argc, argv, shortopts)) != -1) {
        switch (c) {
            case 'a':
                algo = atkin_sieve;
                break;
            case 'e':
                algo = eratosthenes_sieve;
                break;
            case 's':
                data.offset = parse_bigint(optarg, "PMIN");
                data.offset &= ~1ULL; /* force offset to be even. */
                break;
            case 'j':
                data.workers = strtoul(optarg, NULL, 0);
                if (!data.workers) {
                    fprintf(stderr, "Invalid number of workers: \'%s\'\n", optarg);
                    return EXIT_FAILURE;
                }
                break;
            case 'r':
                output_type = OUTPUT_RAW;
                break;
            case 'q':
                output_type = OUTPUT_QUIET;
                break;
            case 'h':
                usage(argc, argv);
                return EXIT_SUCCESS;
            case '?':
            default:
                return EXIT_FAILURE;
        }
    }
    if (argc > optind) {
        data.pmax = parse_bigint(argv[optind], "PMAX");
        if (data.pmax <= data.offset) {
            fprintf(stderr, "Invalid value of PMAX: \'%s\'\n", argv[optind]);
            return EXIT_FAILURE;
        }
    }

    /* Setup the space for prime number crunching. */
    data.psqrt = isqrt(data.pmax);
    data.mem = malloc(PRIME_MEM_WORDS(data.pmax - data.offset) * sizeof(unsigned long));
    if (!data.mem) {
        fprintf(stderr, "Memory allocation failed: %s\n", strerror(errno));
        return EXIT_FAILURE;
    }

    /* Run the prime generator algorithm */
    clock_gettime(CLOCK_MONOTONIC, &start);
    /* Precomputation is required for windowed algorithms. */
    if (data.offset && !data.lowprimes) {
        struct worker_data precompute = {
            .mutex = PTHREAD_MUTEX_INITIALIZER,
            .workers = 1,
            .offset = 0,
            .pmax = data.psqrt,
            .psqrt = isqrt(data.psqrt),
        };
        precompute.mem = malloc(PRIME_MEM_WORDS(data.psqrt) * sizeof(unsigned long));
        if (!precompute.mem) {
            fprintf(stderr, "Memory allocation failed: %s\n", strerror(errno));
            exit(EXIT_FAILURE);
        }
        algo(&precompute);
        data.lowprimes = precompute.mem;
    }
    algo(&data);
    clock_gettime(CLOCK_MONOTONIC, &end);

    /* Compute the amount of time it took. */
    msec = (end.tv_sec - start.tv_sec) * 1000;
    msec += (end.tv_nsec) / 1000000;
    msec -= (start.tv_nsec) / 1000000;
    fprintf(stderr, "Elapsed Time: %llu.%03u seconds\n", msec / 1000, (unsigned int)(msec % 1000));

    /* Print the list of primes. */
    if (output_type == OUTPUT_DECIMAL) {
        unsigned long long p;
        if (!data.offset) fprintf(stdout, "%d\n", 2);
        for (p = data.offset+1; p < data.pmax; p += 2) {
            if (test(p, data.offset, data.mem)) fprintf(stdout, "%llu\n", p);
        }
    }
    /* Write the raw bitmap of primes. */
    /*
     * Using a wheel factorization mod 60, we can improve the memory storage efficiency
     * from 128 integers per long to 128*60/16 integers per long (ie: only 16 possible
     * primes per group of 60 integers), but does this really improve anything vs just
     * throwing the resulting file through gzip?
     *
     * Better yet, store the run-length encoding, aka the prime gaps?
     */
    else if (output_type == OUTPUT_RAW) {
        unsigned long nwords = PRIME_MEM_WORDS(data.pmax - data.offset);
        unsigned long offset = 0;
        while (offset < nwords) {
            unsigned int ret = fwrite(data.mem + offset, sizeof(unsigned long), nwords - offset, stdout);
            if (ret == 0) break;
            offset += ret;
        }
    }
    return 0;
}
