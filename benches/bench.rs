#![feature(allocator_api)]

use bumpalo::Bump;
use criterion::*;
use scoped_arena::Scope;
use std::alloc::{Allocator, Global};

#[derive(Default)]
struct Dummy(u128);

const VEC_COUNT: usize = 100;

fn vec_alloc<T: Default, A: Allocator>(alloc: A, count: usize) {
    let mut vec = Vec::new_in(alloc);
    vec.resize_with(count, T::default);
    std::mem::forget(black_box(vec));
}

fn from_iter<T: Default>(alloc: &Scope<'static>, count: usize) {
    let slice = alloc.to_scope_from_iter((0..count).map(|_| T::default()));
    black_box(slice);
}

fn many<T: Default>(alloc: &Scope<'static>, count: usize) {
    let slice = alloc.to_scope_many_with(count, T::default);
    black_box(slice);
}

fn vec_full<T: Default, A: Allocator>(alloc: A, count: usize) {
    let mut vec = Vec::new_in(alloc);
    vec.resize_with(count, T::default);
    drop(black_box(vec));
}

fn bench_vec_alloc(c: &mut Criterion) {
    let mut group = c.benchmark_group("alloc");
    group.throughput(Throughput::Elements(VEC_COUNT as u64));
    group.bench_function("global", |b| {
        b.iter(|| vec_alloc::<Dummy, _>(Global, VEC_COUNT))
    });

    let mut scope: Scope = Scope::with_capacity(1 << 10);
    let mut bump = Bump::new();

    bump.alloc([0u8; 1024]);
    bump.reset();

    group.bench_function("bump", |b| {
        b.iter(|| {
            vec_alloc::<Dummy, _>(&bump, VEC_COUNT);
            bump.reset();
        })
    });

    group.bench_function("scope", |b| {
        b.iter(|| {
            vec_alloc::<Dummy, _>(&scope, VEC_COUNT);
            scope.reset();
        })
    });

    group.bench_function("scope iter", |b| {
        b.iter(|| {
            from_iter::<Dummy>(&scope, VEC_COUNT);
            scope.reset();
        })
    });

    group.bench_function("scope many", |b| {
        b.iter(|| {
            many::<Dummy>(&scope, VEC_COUNT);
            scope.reset();
        })
    });
}

fn bench_vec_full(c: &mut Criterion) {
    let mut group = c.benchmark_group("full");
    group.throughput(Throughput::Elements(VEC_COUNT as u64));
    group.bench_function("global", |b| {
        b.iter(|| vec_full::<Dummy, _>(Global, VEC_COUNT))
    });

    let mut scope = scoped_arena::Scope::with_capacity(1 << 10);
    let mut bump = Bump::new();

    bump.alloc([0u8; 1024]);
    bump.reset();

    group.bench_function("bump", |b| {
        b.iter(|| {
            vec_full::<Dummy, _>(&bump, VEC_COUNT);
            bump.reset();
        })
    });

    group.bench_function("scope", |b| {
        b.iter(|| {
            vec_full::<Dummy, _>(&scope, VEC_COUNT);
            scope.reset();
        })
    });
}

criterion_group!(benches, bench_vec_alloc, bench_vec_full);
criterion_main!(benches);
