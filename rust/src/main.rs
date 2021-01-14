use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;
use clap::{Arg, App};

const PRIME_WORD_BITS:u64 = 64;
const PRIME_WORD_DENSITY:u64 = PRIME_WORD_BITS*2;

struct WorkerData {
    workers:    u32,    /* Number of worker threads to use. */
    offset:     u64,    /* The minimum prime to start at. */
    pmax:       u64,    /* The maximum prime desired. */
    psqrt:      u32,    /* sqrt(pmax) */
    p:          AtomicU64,
    x:          AtomicU64,
    mem:        Vec::<AtomicU64>,   /* Destination memory for prime data. */
    lowprimes:  Option<*const u64>, /* Table of precomputed low primes. */
}

impl fmt::Debug for WorkerData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WorkerData")
            .field("workers", &self.workers)
            .field("offset", &self.offset)
            .field("pmax", &self.pmax)
            .field("psqrt", &self.psqrt)
            .field("p", &self.p)
            .field("x", &self.x)
            .finish()
    }
}

impl WorkerData {
    /* Clear a bit for the candidate primes. */
    fn clear(&self, p: u64) {
        if (p & 1) == 0 {
            return;     /* Even numbers are not prime. */
        }
        if p <= self.offset {
            return;  /* Ignore numbers below the starting prime. */
        }
        /* Find the bit to examine for primeness. */
        let p = (p-self.offset-1)/2;
        let bit = p % PRIME_WORD_BITS;
        let index = p / PRIME_WORD_BITS;
        self.mem[index as usize].fetch_and(!(1 << bit), Ordering::AcqRel);
    }

    /* Invert a bit for the candidate primes. */
    fn flip(&self, p: u64) {
        if (p & 1) == 0 {
            return;     /* Even numbers are not prime. */
        }
        if p <= self.offset {
            return;  /* Ignore numbers below the starting prime. */
        }
        let p = (p-self.offset-1)/2;
        let bit = p % PRIME_WORD_BITS;
        let index = p / PRIME_WORD_BITS;
        self.mem[index as usize].fetch_xor(1 << bit, Ordering::AcqRel);
    }

    /* Test if a bit is set in the candidate primes. */
    fn test(&self, p: u64) -> bool {
        if (p & 1) == 0 {
            return false;     /* Even numbers are not prime. */
        }
        if p <= self.offset {
            return false;  /* Ignore numbers below the starting prime. */
        }
        let p = (p-self.offset-1)/2;
        let bit = 1u64 << (p % PRIME_WORD_BITS);
        let pword = self.mem[(p / PRIME_WORD_BITS) as usize].load(Ordering::Relaxed);
        (pword & bit) != 0
    }

    /* Test if a precomputed/lowprime bit is set. */
    fn test_lowprime(&self, p: u64) -> bool {
        if (p & 1) == 0 {
            return false;     /* Even numbers are not prime. */
        }
        let p = (p-1)/2; /* Find the bit to examine for primeness. */
        let bit = 1u64 << (p % PRIME_WORD_BITS);
        let pword = match self.lowprimes {
            Some(mem) => unsafe { *mem.offset((p / PRIME_WORD_BITS) as isize) },
            None => 0u64,
        };
        (pword & bit) != 0
    }
}

/* Compute an integer square root. */
fn isqrt(x: u64) -> u32 {
    if x < 2 {
        return x as u32;
    }
    let small = isqrt(x >> 2) << 1;
    let large = small+1;
    let square = (large as u64) * (large as u64);

    if square > x { small } else { large }
}

/*===============================================
 * Sieve of Aitkin
 *===============================================
 */
/* Inner loop of the Sieve of Aktin, for solutions to 4x^2 + y^2 == 1 mod 4. */
fn atkin_inner_4x(data: &WorkerData, xsqr: u64) {
    let mut y = 1u64;
    let xsqr4 = 4*xsqr;

    if xsqr4 >= data.pmax {
        return;
    }
    if xsqr4 < data.offset {
        y = (isqrt(data.offset - xsqr4) | 1) as u64;
    }

    loop {
        let p = xsqr4 + y*y;
        if p >= data.pmax {
            break;
        }
        data.flip(p);
        y += 2;
    }
}


/* Inner loop of the Sieve of Aktin for solutions to 3x^2 + y^2 == 7 mod 12 */
fn atkin_inner_3xplus(data: &WorkerData, xsqr: u64) {
    let mut y = 2u64;

    /*
     * If x^2 is even, then 3x^2 == 0 mod 12, but, 7 is not a quadratic residue
     * mod 12. Therefore there should be no integer solutions for even x^2.
     *
     * If x^2 is odd, then 3x^2 == 3 mod 12, and therefore y^2 == 4 mod 12, which
     * will have solutions for y==2 mod 6 and y==4 mod 6.
     */
    if (xsqr & 1) == 0 {
        return;
    }
    if (3*xsqr) >= data.pmax {
        return;
    }
    if (3*xsqr) < data.offset {
        y = isqrt(data.offset - 3*xsqr) as u64;
        y -= y % 6;
        y += 2;
    }

    loop {
        let p = 3*xsqr + y*y;
        if p >= data.pmax {
            break;
        }
        data.flip(p);
        let p = p + (4*y + 4); /* p = 3x^2 + (y+2)^2 */
        if p >= data.pmax {
            break;
        }
        data.flip(p);
        y += 6;
    }
}

/* Inner loop of the Sieve of Aktin for solutions to 3x^2 - y^2 == 11 mod 12 */
fn atkin_inner_3xminus(data: &WorkerData, x: u32, xsqr: u64)
{
    let mut y = 0u32;

    /* With y < y, this will give solutions in the range 2x^2 < p < 3x^2 */
    /* What the hell is with this comment? */
    if (3*xsqr) < data.offset {
        return;
    }
    if (3*xsqr) >= data.pmax {
        y = isqrt(3*xsqr - data.pmax);
        y -= y % 6;
    }

    /* For x^2 odd, 3x^2 == 3 mod 12, and we seek soltutions with y^2 == 4 mod 12. */
    if (xsqr & 1) != 0 {
        y += 2;
        let mut skip = 6 - (y % 3)*2;
        while y < x {
            let p = 3*xsqr - (y as u64)*(y as u64);
            if p < data.pmax {
                data.flip(p);
            }
            y += skip;
            if skip != 6 {
                skip = 6 - skip;
            }
        }
    }
    /* Otherwise, 3x^2 == 0 mod 12, so we seek solutions with y^2 == 1 mod 12. */
    else {
        y += 1;
        let mut skip =  6 - (y % 3)*2;
        while y < x {
            let p = 3*xsqr - (y as u64)*(y as u64);
            if p < data.pmax {
                data.flip(p);
            }
            y += skip;
            if skip != 6 {
                skip = 6 - skip;
            }
        }
    }
}

fn atkin_clear_squares(data: &WorkerData, p: u64) {
    let psquare = p*p;
    let mut first = psquare;
    if first < data.offset {
        first = data.offset - (data.offset % psquare);
        if (first & 1) == 0 {
            first += psquare;
        }
    }
    for i in (first..data.pmax).step_by(2*psquare as usize) {
        data.clear(i);
    }
}

fn atkin_worker(data: &WorkerData) {
    /* Eliminate squarefree composite numbers. */
    /* The maximum value of x is given by the pmax == 3x^2-y^2 when x=y, or pmax == 2x^2 */
    loop {
        let x = data.x.fetch_add(1, Ordering::Acquire);
        let xsqr = (x as u64)*(x as u64);
        if xsqr >= (data.pmax/2) as u64 {
            break;
        }
        atkin_inner_4x(&data, xsqr);
        atkin_inner_3xplus(&data, xsqr);
        atkin_inner_3xminus(&data, x as u32, xsqr);
    }

    /* Eliminate the squares of primes. */
    loop {
        let p = data.p.fetch_add(PRIME_WORD_DENSITY, Ordering::Acquire);
        if p >= data.psqrt as u64 {
            break;
        }
        for i in (0u64..PRIME_WORD_DENSITY).step_by(2) {
            if data.test_lowprime(p+i) {
                atkin_clear_squares(&data, p+i);
            }
        }
    }
}

fn atkin_sieve(mut data: &mut WorkerData) {
    /* Set all numbers as composite */
    for i in 0..data.mem.len() {
        data.mem[i as usize].store(0u64, Ordering::Relaxed);
    }
    data.flip(3);
    data.p.store(3, Ordering::Relaxed);
    data.x.store(data.offset, Ordering::Relaxed);

    /* The precomputed and working memory can be the same. */
    if let None = data.lowprimes {
        data.lowprimes = Some(data.mem.as_ptr() as *const u64)
    }

    atkin_worker(&mut data);

    data.clear(1);
}

/*===============================================
 * Sieve of Eratosthenes
 *===============================================
 */
fn eratosthenes_clear_multiples(data: &WorkerData, p: u64) {
    let mut first:u64 = 3*p;
    if first < data.offset {
        first = data.offset + p - (data.offset % p);
        if (first & 1) == 0 {
            first = first+p;
        }
    }
    for i in (first..data.pmax).step_by(2*p as usize) {
        data.clear(i);
    }
}

fn eratosthenes_worker(mut data: &mut WorkerData)
{
    loop {
        let p = data.p.fetch_add(PRIME_WORD_DENSITY, Ordering::Acquire);
        if p >= data.psqrt as u64 {
            break;
        }
        for i in (0u64..PRIME_WORD_DENSITY).step_by(2) {
            if data.test_lowprime(p+i) {
                eratosthenes_clear_multiples(&mut data, p+i);
            }
        }
    }
}

fn eratosthenes_sieve(mut data: &mut WorkerData) {
    /* Initialize all numbers as prime. */
    for i in 0..data.mem.len() {
        data.mem[i as usize].store(!0u64, Ordering::Relaxed);
    }
    if data.offset <= 2 {
        data.clear(1);
    }
    data.p.store(3, Ordering::Relaxed);
    data.x.store(data.offset, Ordering::Relaxed);

    /* The precomputed and working memory can be the same. */
    if let None = data.lowprimes {
        data.lowprimes = Some(data.mem.as_ptr() as *const u64)
    }

    eratosthenes_worker(&mut data);
}

/*===============================================
 * Algorithm Setup
 *===============================================
 */

/* Parse an integer, with possible SI or binary suffixes. */
fn parse_bigint(bigstr: &str) -> Option<u64> {
    let suffix = bigstr.trim_start_matches(char::is_numeric);
    let digits = &bigstr[0..bigstr.len()-suffix.len()];
    let base = match suffix {
        "" => 1u64,
        "k" => 1000u64,
        "M" => 1000000u64,
        "G" => 1000000000u64,
        "T" => 1000000000000u64,
        "ki" => 1024u64,
        "Mi" => (1024u64*1024u64),
        "Gi" => (1024u64*1024u64*1024u64),
        "Ti" => (1024u64*1024u64*1024u64*1024u64),
        _ => return None
    };
    match digits.parse::<u64>() {
        Ok(n) => Some(n * base),
        Err(_e) => None
    }
}

fn main() {
    let matches = App::new("Prime Grind")
        .version("0.1.0")
        .author("Owen Kirby <oskirby@gmail.com>")
        .about("Experiments with prime number generating algorithms")
        .arg(Arg::with_name("pmax")
            .help("The maximum prime to search for")
            .index(1)
            .required(true))
        .arg(Arg::with_name("atkin")
            .short("a")
            .long("atikin")
            .help("Use the sieve of Atkin algorithm"))
        .arg(Arg::with_name("eratosthenes")
            .short("e")
            .long("eratosthenes")
            .help("Use the sieve of Eratosthenes algorithm"))
        .arg(Arg::with_name("precompute")
            .short("p")
            .long("precomute")
            .takes_value(true)
            .help("Use a file of precomputed primes"))
        .arg(Arg::with_name("start")
            .short("s")
            .long("start")
            .takes_value(true)
            .help("Starting number to search from"))
        .arg(Arg::with_name("threads")
            .short("j")
            .long("threads")
            .takes_value(true)
            .help("Number of worker threads"))
        .arg(Arg::with_name("raw")
            .short("r")
            .long("raw")
            .help("Output primes as a raw bitmap"))
        .arg(Arg::with_name("quiet")
            .short("q")
            .long("quiet")
            .help("Output nothing, perform timing only"))
        .get_matches();
    
    /* Parse the maximum prime. */
    let pmax = match parse_bigint(matches.value_of("pmax").unwrap()) {
        Some(n) => n,
        None => {
            println!("Unable to parse pmax");
            std::process::exit(0);
        },
    };
    let pwords = ((pmax + PRIME_WORD_DENSITY - 1) / PRIME_WORD_DENSITY) as usize;

    /* Setup the prime finding worker data. */
    let mut data = WorkerData {
        workers: 1,
        offset: 0,
        pmax: pmax,
        psqrt: isqrt(pmax),
        p: AtomicU64::new(0),
        x: AtomicU64::new(0),
        mem: Vec::<AtomicU64>::with_capacity(pwords),
        lowprimes: None,
    };
    unsafe { data.mem.set_len(pwords); }

    /* Grab a timestamp to measure performance. */
    let start = Instant::now();

    /* Compute! */
    if matches.is_present("atkin") {
        atkin_sieve(&mut data);
    }
    else {
        eratosthenes_sieve(&mut data);
    }

    /* Output the elapsed time. */
    eprintln!("Elapsed Time: {}", start.elapsed().as_secs_f64());

    /* Print out the primes. */
    if data.offset <= 2 {
        println!("2");
    }
    for p in (data.offset+1..data.pmax).step_by(2) {
        if data.test(p) {
            println!("{}", p);
        }
    }
}