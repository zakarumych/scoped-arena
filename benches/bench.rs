#![feature(allocator_api)]

use bumpalo::Bump;
use criterion::*;
use scoped_arena::Scope;
use std::alloc::{Allocator, Global};

#[derive(Default)]
struct Small(u8);

#[derive(Default)]
struct Big([usize; 32]);

const ALLOCATIONS: usize = 10_000;
const VEC_COUNT: usize = 100;

fn vec_alloc<T: Default, A: Allocator>(alloc: A, count: usize) {
    let mut vec = Vec::new_in(alloc);
    vec.extend((0..count).map(|_| T::default()));
    std::mem::forget(black_box(vec));
}

fn from_iter<T: Default>(alloc: &Scope<'static>, count: usize) {
    let slice = alloc.to_scope_from_iter((0..count).map(|_| T::default()));
    black_box(slice);
}

fn vec_full<T: Default, A: Allocator>(alloc: A, count: usize) {
    let mut vec = Vec::new_in(alloc);
    vec.extend((0..count).map(|_| T::default()));
    drop(black_box(vec));
}

fn bench_vec_alloc(c: &mut Criterion) {
    let mut group = c.benchmark_group("alloc");
    group.throughput(Throughput::Elements(VEC_COUNT as u64));
    group.bench_function("global", |b| {
        b.iter(|| vec_alloc::<Small, _>(Global, VEC_COUNT))
    });

    let mut scope: Scope = Scope::with_capacity(1 << 10);
    let mut bump = Bump::new();

    bump.alloc([0u8; 1024]);
    bump.reset();

    group.bench_function("scope", |b| {
        b.iter(|| {
            vec_alloc::<Small, _>(&scope, VEC_COUNT);
            scope.reset();
        })
    });

    group.bench_function("bump", |b| {
        b.iter(|| {
            vec_alloc::<Small, _>(&bump, VEC_COUNT);
            bump.reset();
        })
    });

    group.bench_function("scope iter", |b| {
        b.iter(|| {
            from_iter::<Small>(&scope, VEC_COUNT);
            scope.reset();
        })
    });
}

fn bench_vec_full(c: &mut Criterion) {
    let mut group = c.benchmark_group("full");
    group.throughput(Throughput::Elements(VEC_COUNT as u64));
    group.bench_function("global", |b| {
        b.iter(|| vec_full::<Small, _>(Global, VEC_COUNT))
    });

    let mut scope = scoped_arena::Scope::with_capacity(1 << 10);
    let mut bump = Bump::new();

    bump.alloc([0u8; 1024]);
    bump.reset();

    group.bench_function("scope", |b| {
        b.iter(|| {
            vec_full::<Small, _>(&scope, VEC_COUNT);
            scope.reset();
        })
    });

    group.bench_function("bump", |b| {
        b.iter(|| {
            vec_full::<Small, _>(&bump, VEC_COUNT);
            bump.reset();
        })
    });
}

criterion_group!(benches, bench_vec_alloc, bench_vec_full);
criterion_main!(benches);
