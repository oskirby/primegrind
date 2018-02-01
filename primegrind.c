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
#define PRIME_MEM_WORDS(_p_)    (((_p_) + (PRIME_WORD_BITS * 2 - 1)) / (PRIME_WORD_BITS * 2))

/* Flip a bit corresponding to a potential prime, p */
static inline void
flip(unsigned long long p, unsigned long *mem)
{
    if (p & 1) {
        p = (p-1)/2;
        __atomic_fetch_xor(&mem[p / PRIME_WORD_BITS], (1UL << (p % PRIME_WORD_BITS)), __ATOMIC_ACQUIRE);
    }
}

static inline void
clear(unsigned long long p, unsigned long *mem)
{
    if (p & 1) {
        p = (p-1)/2;
        __atomic_fetch_and(&mem[p / PRIME_WORD_BITS], ~(1UL << (p % PRIME_WORD_BITS)), __ATOMIC_ACQUIRE);
    }
}

static inline int
test(unsigned long long p, unsigned long *mem)
{
    if (p & 1) {
        p = (p-1)/2;
        return (mem[p / PRIME_WORD_BITS] >> (p % PRIME_WORD_BITS)) & 1;
    } else {
        return 0;
    }
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
atkin_inner(unsigned long x, unsigned long long maxprime, unsigned long *mem)
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
        if (p >= maxprime) break;
        flip(p, mem);
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
            if (p >= maxprime) break;
            flip(p, mem);
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
            if (p < maxprime) flip(p, mem);
            y += skip;
            if (skip != 6) skip = 6 - skip;
        }
    }
}

struct worker_data {
    pthread_mutex_t mutex;
    unsigned long long pmax;
    unsigned long long p;
    unsigned long long x;
    unsigned long psqrt;
    unsigned long *mem;
};

static void
atkin_clear_squares(unsigned long p, unsigned long long maxprime, unsigned long *mem)
{
    unsigned long long p2 = (unsigned long long)p * p;
    unsigned long long i;
    for (i = p2; i < maxprime; i += p2) {
        clear(i, mem);
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
        atkin_inner(x, data->pmax, data->mem);
    } while(1);

    /* Eliminate the squares of primes. */
    pthread_mutex_lock(&data->mutex);
    while (data->p < data->psqrt) {
        /* Find the next prime. */
        unsigned long long i;
        unsigned long long p = data->p;
        data->p += 2;
        if (!test(p, data->mem)) {
            continue;
        }

        /* Let other threads do work while we mark off square multiples of this prime. */
        pthread_mutex_unlock(&data->mutex);
        atkin_clear_squares(p, data->pmax, data->mem);
        pthread_mutex_lock(&data->mutex);
    }
    pthread_mutex_unlock(&data->mutex);
}

/* The Sieve of Atkin */
static void
atkin_sieve(unsigned long long maxprime, unsigned long *mem, unsigned int workers)
{
    unsigned long long p;
    struct worker_data data = {
        .mutex = PTHREAD_MUTEX_INITIALIZER,
        .pmax = maxprime,
        .psqrt = isqrt(maxprime),
        .p = 3,
        .x = 0,
        .mem = mem
    };

    /* Set all numbers as composite */
    memset(mem, 0, sizeof(unsigned long) * PRIME_MEM_WORDS(maxprime));
    flip(3, mem);

    /* Go Parallel */
    if (workers > 1) {
        pthread_t worker_threads[workers];
        unsigned int i;

        /* Launch workers. */
        for (i = 0; i < workers; i++) {
            pthread_create(&worker_threads[i], NULL, atkin_worker, &data);
        } /* for */
        /* Wait for the workers to finish. */
        for (i = 0; i < workers; i++) {
            pthread_join(worker_threads[i], NULL);
        }
    }
    /* Single-threaded */
    else {
        /* Eliminate squarefree composite numbers. */
        for (data.x = 0; data.x < data.psqrt; data.x++) {
            atkin_inner(data.x, data.pmax, data.mem);
        }
        /* Clear out the multiples of squares.  */
        while (data.p < data.psqrt) {
            if (test(data.p, data.mem)) {
                atkin_clear_squares(data.p, data.pmax, data.mem);
            }
            data.p += 2;
        }
    }
}

static void *
eratosthenes_worker(void *arg)
{
    struct worker_data *data = arg;

    pthread_mutex_lock(&data->mutex);
    while (data->p < data->psqrt) {
        /* Find the next prime. */
        unsigned long long i;
        unsigned long long p = data->p;
        data->p += 2;
        if (!test(p, data->mem)) {
            continue;
        }

        /* Let other threads do work while we mark off composite multiples of this prime. */
        pthread_mutex_unlock(&data->mutex);
        for (i = p + p; i < data->pmax; i += p) clear(i, data->mem);
        pthread_mutex_lock(&data->mutex);
    }
    pthread_mutex_unlock(&data->mutex);
}

/* The Sieve of Eratosthenes */
static void
eratosthenes_sieve(unsigned long long maxprime, unsigned long *mem, unsigned int workers)
{
    struct worker_data data = {
        .mutex = PTHREAD_MUTEX_INITIALIZER,
        .pmax = maxprime,
        .psqrt = isqrt(maxprime),
        .p = 3,
        .mem = mem
    };

    /* Set all numbers as prime */
    memset(mem, ~0, sizeof(unsigned long) * PRIME_MEM_WORDS(maxprime));

    /* Multithreaded version. */
    if (workers > 1) {
        pthread_t worker_threads[workers];
        unsigned int i;
        /* Launch workers. */
        for (i = 0; i < workers; i++) {
            pthread_create(&worker_threads[i], NULL, eratosthenes_worker, &data);
        } /* for */
        /* Wait for the workers to finish. */
        for (i = 0; i < workers; i++) {
            pthread_join(worker_threads[i], NULL);
        }
    }
    /* Single-threaded version */
    else {
        while (data.p < data.psqrt) {
            if (test(data.p, data.mem)) {
                unsigned long long i;
                for (i = data.p * 2; i < data.pmax; i += data.p) clear(i, data.mem);
            }
            data.p += 2;
        }
    }
}

static void
usage(int argc, char * const argv[])
{
    fprintf(stdout, "Usage: %s [options] [MAXPRIME]\n\n", argv[0]);
    fprintf(stdout, "Search for prime numbers less than MAXPRIME\n\n");
    fprintf(stdout, "options:\n");
    fprintf(stdout, "\t-a       use the Sieve of Aktin algorithm\n");
    fprintf(stdout, "\t-e       use the Sieve of Eratosthenes algorithm\n");
    fprintf(stdout, "\t-j NUM   distribute work amongst NUM threads");
    fprintf(stdout, "\t-h       display this message and exit\n");
}

#define OUTPUT_QUIET    0
#define OUTPUT_DECIMAL  1
#define OUTPUT_RAW      2

int
main(int argc, char * const argv[])
{
    struct timespec start, end;

    unsigned long long maxprime = 1000000;
    unsigned long long msec;
    unsigned long long p;
    unsigned long *mem;
    unsigned int workers = 1;
    void (*algo)(unsigned long long, unsigned long *, unsigned int) = atkin_sieve;
    const char *shortopts = "aerqj:h";
    unsigned int output_type = OUTPUT_DECIMAL;

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
            case 'j':
                workers = strtoul(optarg, NULL, 0);
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
        const char *maxstr = argv[optind];
        char *e;
        maxprime = strtoull(maxstr, &e, 0);
        if (maxprime == 0) {
            fprintf(stderr, "Invalid value of MAXPRIME: \'%s\'\n", maxstr);
            return EXIT_FAILURE;
        }
        /* Handle suffixes to make it easier to grok large numbers. */
        switch (e[0] + (e[0] ? e[1]<<8 : 0)) {
            case 'k':
                maxprime *= 1000ULL;
                break;
            case 'M':
                maxprime *= 1000000ULL;
                break;
            case 'G':
                maxprime *= 1000000000ULL;
                break;
            case 'T':
                maxprime *= 1000000000000ULL;
                break;
            case 0:
                break;
            default:
                fprintf(stderr, "Invalid value of MAXPRIME: \'%s\'\n", maxstr);
                return EXIT_FAILURE;
        }
    }

    /* Setup the memory space for our prime number crunching */
    mem = malloc(PRIME_MEM_WORDS(maxprime) * sizeof(unsigned long));
    if (!mem) {
        fprintf(stderr, "Memory allocation failed: %s\n", strerror(errno));
        return EXIT_FAILURE;
    }

    /* Run the prime generator algorithm */
    clock_gettime(CLOCK_MONOTONIC, &start);
    algo(maxprime, mem, workers);
    clock_gettime(CLOCK_MONOTONIC, &end);

    /* Compute the amount of time it took. */
    msec = (end.tv_sec - start.tv_sec) * 1000;
    msec += (end.tv_nsec) / 1000000;
    msec -= (start.tv_nsec) / 1000000;
    fprintf(stderr, "Elapsed Time: %llu.%03u seconds\n", msec / 1000, (unsigned int)(msec % 1000));

    /* Print the list of primes. */
    if (output_type == OUTPUT_DECIMAL) {
        fprintf(stdout, "%d\n", 2);
        for (p = 3; p < maxprime; p += 2) {
            if (test(p, mem)) fprintf(stdout, "%llu\n", p);
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
        unsigned long nwords = PRIME_MEM_WORDS(maxprime);
        unsigned long offset = 0;
        while (offset < nwords) {
            unsigned int ret = fwrite(mem + offset, sizeof(unsigned long), nwords - offset, stdout);
            if (ret == 0) break;
            offset += ret;
        }
    }
    return 0;
}
