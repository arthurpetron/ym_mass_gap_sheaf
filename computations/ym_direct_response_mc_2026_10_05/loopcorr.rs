//! ymbot scratch: temporal correlators of spatial l x l Wilson loops (F = Tr = 2 a0),
//! raw and APE-smeared, single-position ("local") and zero-momentum ("zm").
//! Output: per-config records (binary f64) for offline jackknife.
use std::io::Write;
use std::time::Instant;
use ym_simulations::*;

fn dot(a: Su2, b: Su2) -> f64 { a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3] }

fn main() {
    let mut l = 16usize; let mut beta = 2.4f64; let mut therm = 500usize; let mut meas = 1000usize;
    let mut interval = 5usize; let mut overrelax = 4usize; let mut sides = vec![1usize,2,3,4];
    let mut smear = vec![0usize, 10, 25]; let mut alpha = 0.5f64; let mut seed = 1u64;
    let mut threads = 4usize; let mut out = String::from("out.bin");
    let argv: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < argv.len() {
        let k = argv[i].clone(); let v = argv[i+1].clone(); i += 2;
        match k.as_str() {
            "--L" => l = v.parse().unwrap(), "--beta" => beta = v.parse().unwrap(),
            "--therm" => therm = v.parse().unwrap(), "--meas" => meas = v.parse().unwrap(),
            "--interval" => interval = v.parse().unwrap(), "--overrelax" => overrelax = v.parse().unwrap(),
            "--sides" => sides = v.split(',').map(|s| s.parse().unwrap()).collect(),
            "--smear" => smear = v.split(',').map(|s| s.parse().unwrap()).collect(),
            "--alpha" => alpha = v.parse().unwrap(), "--seed" => seed = v.parse().unwrap(),
            "--threads" => threads = v.parse().unwrap(), "--out" => out = v,
            o => panic!("unknown {o}"),
        }
    }
    smear.sort(); smear.dedup();
    let tmax = l / 2;
    let mut lat = Lattice::new_hot(l, seed);
    let classes = build_classes(&lat);
    let nb = Neighbors::new(&lat.geom());
    let ns = l * l * l; // spatial sites per slice (x0 = time is slowest index)
    let t0 = Instant::now();
    let mut sweep_idx = 0u64;
    for _ in 0..therm { sweep(&mut lat, beta, overrelax, sweep_idx, seed, threads, &classes, &nb); sweep_idx += 1; }
    eprintln!("L={l} beta={beta} therm {therm} done {:.1}s plaq={:.5}", t0.elapsed().as_secs_f64(), lat.avg_plaquette());
    let mut f = std::fs::File::create(&out).unwrap();
    // header
    let hdr = format!("L={l} beta={beta} sides={:?} smear={:?} alpha={alpha} tmax={tmax} interval={interval} overrelax={overrelax} seed={seed}\n", sides, smear);
    f.write_all(hdr.as_bytes()).unwrap();
    let mut buf_a = lat.links.clone(); let mut buf_b = lat.links.clone();
    for m in 0..meas {
        for _ in 0..interval { sweep(&mut lat, beta, overrelax, sweep_idx, seed, threads, &classes, &nb); sweep_idx += 1; }
        buf_a.copy_from_slice(&lat.links);
        let mut done = 0usize;
        let mut rec: Vec<f64> = Vec::new();
        rec.push(lat.avg_plaquette());
        for &lev in &smear {
            while done < lev { ape_smear_spatial_into(&buf_a, &mut buf_b, &nb, alpha, threads); std::mem::swap(&mut buf_a, &mut buf_b); done += 1; }
            let links = &buf_a;
            for &side in &sides {
                // values[t][s*3+plane]
                let vals: Vec<Vec<f64>> = std::thread::scope(|sc| {
                    let mut hs = Vec::new();
                    for t in 0..l {
                        let nb = &nb;
                        hs.push(sc.spawn(move || {
                            let mut v = vec![0f64; ns * 3];
                            for s in 0..ns {
                                let x = t * ns + s;
                                // line products
                                let line = |start: usize, dir: usize| -> Su2 {
                                    let mut p = ID; let mut y = start;
                                    for _ in 0..side { p = mul(p, lget(links, y, dir)); y = nb.fwd(y, dir); }
                                    p
                                };
                                let mut k = 0;
                                for a in 1..4 { for b in (a+1)..4 {
                                    let xa = nb.shift_n(x, a, side, true);
                                    let xb = nb.shift_n(x, b, side, true);
                                    let pa = mul(line(x, a), line(xa, b));
                                    let pb = mul(line(x, b), line(xb, a));
                                    v[s*3+k] = 2.0 * dot(pa, pb); // Tr(pa pb^dag) = 2 a0
                                    k += 1;
                                }}
                            }
                            v
                        }));
                        if hs.len() >= threads.max(1) { /* simple throttle: join oldest */ }
                    }
                    hs.into_iter().map(|h| h.join().unwrap()).collect()
                });
                let n = (ns * 3) as f64;
                let mean: f64 = vals.iter().map(|v| v.iter().sum::<f64>()).sum::<f64>() / (n * l as f64);
                let slice: Vec<f64> = vals.iter().map(|v| v.iter().sum::<f64>()).collect();
                rec.push(mean);
                for tau in 0..=tmax {
                    let mut loc = 0.0; let mut zm = 0.0;
                    for t in 0..l {
                        let t2 = (t + tau) % l;
                        let (va, vb) = (&vals[t], &vals[t2]);
                        let mut s = 0.0; for j in 0..ns*3 { s += va[j]*vb[j]; }
                        loc += s; zm += slice[t]*slice[t2];
                    }
                    rec.push(loc / (n * l as f64));   // <f f> local, unsubtracted
                    rec.push(zm / (n * l as f64));    // <S S>/n, unsubtracted
                }
            }
        }
        let bytes: Vec<u8> = rec.iter().flat_map(|x| x.to_le_bytes()).collect();
        f.write_all(&bytes).unwrap();
        if m % 50 == 0 { eprintln!("meas {m}/{meas} {:.1}s plaq={:.5} reclen={}", t0.elapsed().as_secs_f64(), rec[0], rec.len()); f.flush().unwrap(); }
    }
    eprintln!("done {:.1}s", t0.elapsed().as_secs_f64());
}
