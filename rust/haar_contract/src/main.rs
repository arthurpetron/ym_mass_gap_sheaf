//! Exact SU(2) Haar network contraction — the hot core of
//! `computations/exact_haar_network.py`, ported for memory/speed
//! (work_plan §16i next attack, evaluation-technology item).
//!
//! Protocol: JSON on stdin
//!   { "factors": [ [ [ [[var,exp],...],  [[power,"num","den"],...] ], ... ], ... ],
//!     "free_links": [ ... ],
//!     "max_monomials": u64 }
//! i.e. each factor is a list of (monomial, spoly) pairs; monomial a
//! list of (var_id, exponent) with var_id = 4*link + comp; spoly a
//! list of (s-power, numerator, denominator) with big-int strings.
//! Output: {"ok": true, "scalar": [[power,"num","den"],...]} — the
//! fully contracted value — or {"ok": false, "err": "..."}.
//!
//! Faithful port of: p_mul (with monomial merge + cap),
//! integrate_link (exact S^3 moment formula), p_reduce_units
//! (z^2 -> 1 - w^2 - x^2 - y^2 canonicalization), and the
//! greedy elimination of `_eliminate_all` (merge the factors
//! touching the cheapest link, integrate, reduce).  Exact rational
//! arithmetic throughout (num-bigint); no floats.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use serde_json::Value;
use std::collections::HashMap;
use std::io::Read;
use std::str::FromStr;

type Mono = Vec<(u8, u8)>; // sorted (var, exp)
type SPoly = HashMap<u32, BigRational>;
type Poly = HashMap<Mono, SPoly>;

fn sp_add_into(acc: &mut SPoly, p: &SPoly, c: &BigRational) {
    if c.is_zero() {
        return;
    }
    for (k, v) in p {
        let nv = acc
            .get(k)
            .cloned()
            .unwrap_or_else(BigRational::zero)
            + v * c;
        if nv.is_zero() {
            acc.remove(k);
        } else {
            acc.insert(*k, nv);
        }
    }
}

fn sp_mul(a: &SPoly, b: &SPoly) -> SPoly {
    let mut out: SPoly = HashMap::new();
    for (ka, va) in a {
        for (kb, vb) in b {
            let k = ka + kb;
            let nv = out
                .get(&k)
                .cloned()
                .unwrap_or_else(BigRational::zero)
                + va * vb;
            if nv.is_zero() {
                out.remove(&k);
            } else {
                out.insert(k, nv);
            }
        }
    }
    out
}

fn mono_mul(m1: &Mono, m2: &Mono) -> Mono {
    if m1.is_empty() {
        return m2.clone();
    }
    if m2.is_empty() {
        return m1.clone();
    }
    let mut d: HashMap<u8, u8> = HashMap::new();
    for (v, e) in m1.iter().chain(m2.iter()) {
        *d.entry(*v).or_insert(0) += e;
    }
    let mut out: Mono = d.into_iter().collect();
    out.sort_unstable();
    out
}

fn p_add_into(acc: &mut Poly, m: Mono, sp: SPoly, c: &BigRational) {
    let slot = acc.entry(m.clone()).or_insert_with(HashMap::new);
    sp_add_into(slot, &sp, c);
    if slot.is_empty() {
        acc.remove(&m);
    }
}

fn p_mul(a: &Poly, b: &Poly, max_out: usize) -> Result<Poly, String> {
    let mut out: Poly = HashMap::new();
    let (small, big) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    for (ma, sa) in small {
        for (mb, sb) in big {
            let m = mono_mul(ma, mb);
            let sp = sp_mul(sa, sb);
            let slot = out.entry(m.clone()).or_insert_with(HashMap::new);
            let one = BigRational::one();
            sp_add_into(slot, &sp, &one);
            if slot.is_empty() {
                out.remove(&m);
            }
        }
        if out.len() > max_out {
            return Err(format!("product exceeded {} monomials", max_out));
        }
    }
    Ok(out)
}

/// z^2 -> 1 - w^2 - x^2 - y^2 canonicalization (unit-norm ideal).
fn p_reduce_units(p: Poly) -> Poly {
    let mut work: Vec<(Mono, SPoly, BigRational)> = p
        .into_iter()
        .map(|(m, sp)| (m, sp, BigRational::one()))
        .collect();
    let mut out: Poly = HashMap::new();
    while let Some((m, sp, coef)) = work.pop() {
        // find a z-variable (var % 4 == 3) with exponent >= 2
        let mut target: Option<(u8, u8)> = None;
        for (v, e) in &m {
            if v % 4 == 3 && *e >= 2 {
                target = Some((*v, *e));
                break;
            }
        }
        match target {
            None => {
                p_add_into(&mut out, m, sp, &coef);
            }
            Some((v, e)) => {
                let base = v - 3;
                let rest: Mono = m
                    .iter()
                    .cloned()
                    .filter(|(vv, _)| *vv != v)
                    .collect();
                let low = if e > 2 {
                    mono_mul(&rest, &vec![(v, e - 2)])
                } else {
                    rest
                };
                let subs: [(Mono, i32); 4] = [
                    (vec![], 1),
                    (vec![(base, 2)], -1),
                    (vec![(base + 1, 2)], -1),
                    (vec![(base + 2, 2)], -1),
                ];
                for (sub, sign) in subs.iter() {
                    let nm = mono_mul(&low, sub);
                    let c = &coef
                        * BigRational::from_integer(BigInt::from(*sign));
                    work.push((nm, sp.clone(), c));
                }
            }
        }
    }
    out
}

fn dfact(k: u32) -> BigInt {
    let mut out = BigInt::one();
    for i in 1..=k {
        out *= 2 * i - 1;
    }
    out
}

fn factorial(k: u32) -> BigInt {
    let mut out = BigInt::one();
    for i in 2..=k {
        out *= i;
    }
    out
}

fn moment(exps: [u8; 4]) -> BigRational {
    if exps.iter().any(|e| e % 2 == 1) {
        return BigRational::zero();
    }
    let halves: Vec<u32> = exps.iter().map(|e| (*e as u32) / 2).collect();
    let a: u32 = halves.iter().sum();
    let mut num = BigInt::one();
    for h in &halves {
        num *= dfact(*h);
    }
    let den = BigInt::from(2u32).pow(a) * factorial(a + 1);
    BigRational::new(num, den)
}

fn integrate_link(p: &Poly, link: u8) -> Poly {
    let base = 4 * link;
    let mut out: Poly = HashMap::new();
    for (m, sp) in p {
        let mut exps = [0u8; 4];
        let mut rest: Mono = Vec::with_capacity(m.len());
        for (v, e) in m {
            if *v >= base && *v < base + 4 {
                exps[(*v - base) as usize] = *e;
            } else {
                rest.push((*v, *e));
            }
        }
        let mom = moment(exps);
        if mom.is_zero() {
            continue;
        }
        p_add_into(&mut out, rest, sp.clone(), &mom);
    }
    out
}

fn p_links(p: &Poly) -> std::collections::HashSet<u8> {
    let mut s = std::collections::HashSet::new();
    for m in p.keys() {
        for (v, _) in m {
            s.insert(v / 4);
        }
    }
    s
}

/// Greedy elimination (the `_eliminate_all` structure): pick the
/// link minimizing the product of touched-factor sizes; merge,
/// integrate, unit-reduce.
fn eliminate_all(
    mut facs: Vec<Poly>,
    free: &std::collections::HashSet<u8>,
    max_monomials: usize,
) -> Result<SPoly, String> {
    let mut todo: std::collections::HashSet<u8> =
        std::collections::HashSet::new();
    for f in &facs {
        for l in p_links(f) {
            if free.contains(&l) {
                todo.insert(l);
            }
        }
    }
    while !todo.is_empty() {
        // choose cheapest link
        let mut best: Option<(u8, f64)> = None;
        for l in &todo {
            let mut cost = 0f64; // log-cost to avoid overflow
            for f in &facs {
                if p_links(f).contains(l) {
                    cost += (f.len().max(1) as f64).ln();
                }
            }
            if best.is_none() || cost < best.unwrap().1 {
                best = Some((*l, cost));
            }
        }
        let (link, _c) = best.unwrap();
        // estimated full-merge size: product of touched sizes
        let mut est: f64 = 0.0;
        for f in &facs {
            if p_links(f).contains(&link) {
                est += (f.len().max(1) as f64).ln();
            }
        }
        if est > (max_monomials as f64).ln() * 1.10 {
            // pair-premerge fallback: multiply the two cheapest
            // factors sharing any live link, put back, retry
            let mut bp: Option<(usize, usize, usize)> = None;
            for i in 0..facs.len() {
                let li: std::collections::HashSet<u8> = p_links(&facs[i])
                    .intersection(&todo).cloned().collect();
                if li.is_empty() { continue; }
                for k in (i + 1)..facs.len() {
                    let lk = p_links(&facs[k]);
                    if li.iter().any(|l| lk.contains(l)) {
                        let pp = facs[i].len().max(1)
                            * facs[k].len().max(1);
                        if bp.is_none() || pp < bp.unwrap().2 {
                            bp = Some((i, k, pp));
                        }
                    }
                }
            }
            if let Some((i, k, _pp)) = bp {
                let fk = facs.remove(k);
                let fi = facs.remove(i);
                let prod = p_reduce_units(p_mul(&fi, &fk,
                                                max_monomials)?);
                facs.push(prod);
                continue;
            }
        }
        let mut touched: Vec<Poly> = Vec::new();
        let mut rest: Vec<Poly> = Vec::new();
        for f in facs.into_iter() {
            if p_links(&f).contains(&link) {
                touched.push(f);
            } else {
                rest.push(f);
            }
        }
        touched.sort_by_key(|f| f.len());
        let mut merged: Poly = HashMap::new();
        merged.insert(vec![], {
            let mut sp = HashMap::new();
            sp.insert(0u32, BigRational::one());
            sp
        });
        for f in &touched {
            merged = p_mul(&merged, f, max_monomials)?;
            merged = p_reduce_units(merged);
        }
        let integrated = integrate_link(&merged, link);
        let reduced = p_reduce_units(integrated);
        rest.push(reduced);
        facs = rest;
        todo.remove(&link);
    }
    // final product
    let mut out: Poly = HashMap::new();
    out.insert(vec![], {
        let mut sp = HashMap::new();
        sp.insert(0u32, BigRational::one());
        sp
    });
    for f in &facs {
        out = p_mul(&out, f, max_monomials)?;
    }
    // scalar extraction
    let mut scalar: SPoly = HashMap::new();
    for (m, sp) in out {
        if !m.is_empty() {
            return Err(format!("not fully contracted: {:?}", m));
        }
        scalar = sp;
    }
    Ok(scalar)
}

fn parse_input(v: &Value) -> Result<(Vec<Poly>, std::collections::HashSet<u8>, usize), String> {
    let factors_v = v["factors"].as_array().ok_or("factors")?;
    let mut factors: Vec<Poly> = Vec::new();
    for fv in factors_v {
        let mut poly: Poly = HashMap::new();
        for pair in fv.as_array().ok_or("factor")? {
            let arr = pair.as_array().ok_or("pair")?;
            let mono_v = arr[0].as_array().ok_or("mono")?;
            let mut mono: Mono = Vec::new();
            for me in mono_v {
                let m2 = me.as_array().ok_or("mono entry")?;
                mono.push((
                    m2[0].as_u64().ok_or("var")? as u8,
                    m2[1].as_u64().ok_or("exp")? as u8,
                ));
            }
            mono.sort_unstable();
            let mut sp: SPoly = HashMap::new();
            for se in arr[1].as_array().ok_or("spoly")? {
                let s3 = se.as_array().ok_or("spoly entry")?;
                let pow = s3[0].as_u64().ok_or("pow")? as u32;
                let num = BigInt::from_str(s3[1].as_str().ok_or("num")?)
                    .map_err(|e| e.to_string())?;
                let den = BigInt::from_str(s3[2].as_str().ok_or("den")?)
                    .map_err(|e| e.to_string())?;
                sp.insert(pow, BigRational::new(num, den));
            }
            poly.insert(mono, sp);
        }
        factors.push(poly);
    }
    let mut free = std::collections::HashSet::new();
    for l in v["free_links"].as_array().ok_or("free_links")? {
        free.insert(l.as_u64().ok_or("link")? as u8);
    }
    let maxm = v["max_monomials"].as_u64().unwrap_or(3_000_000) as usize;
    Ok((factors, free, maxm))
}

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let v: Value = match serde_json::from_str(&input) {
        Ok(v) => v,
        Err(e) => {
            println!("{{\"ok\": false, \"err\": \"parse: {}\"}}", e);
            return;
        }
    };
    let (factors, free, maxm) = match parse_input(&v) {
        Ok(t) => t,
        Err(e) => {
            println!("{{\"ok\": false, \"err\": \"input: {}\"}}", e);
            return;
        }
    };
    match eliminate_all(factors, &free, maxm) {
        Ok(scalar) => {
            let mut terms: Vec<String> = Vec::new();
            let mut keys: Vec<u32> = scalar.keys().cloned().collect();
            keys.sort_unstable();
            for k in keys {
                let r = &scalar[&k];
                let (num, den) = (r.numer(), r.denom());
                let (num, den) = if den.is_negative() {
                    (-num.clone(), -den.clone())
                } else {
                    (num.clone(), den.clone())
                };
                terms.push(format!(
                    "[{},\"{}\",\"{}\"]",
                    k, num, den
                ));
            }
            println!("{{\"ok\": true, \"scalar\": [{}]}}", terms.join(","));
        }
        Err(e) => {
            println!("{{\"ok\": false, \"err\": \"{}\"}}", e);
        }
    }
}
