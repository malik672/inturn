use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use inturn::BytesInterner;
use std::collections::HashMap;

fn bench_do_intern(c: &mut Criterion) {
    let interner = BytesInterner::new();

    let mut group = c.benchmark_group("do_intern");

    // Benchmark single small string
    group.bench_function("single_small_string", |b| {
        b.iter(|| {
            black_box(interner.intern(black_box(b"hello")))
        });
    });

    // Benchmark single medium string
    group.bench_function("single_medium_string", |b| {
        let medium_str = b"this_is_a_medium_length_string_for_testing_purposes";
        b.iter(|| {
            black_box(interner.intern(black_box(medium_str)))
        });
    });

    // Benchmark single large string
    group.bench_function("single_large_string", |b| {
        let large_str = b"this_is_a_very_long_string_that_contains_many_characters_and_is_designed_to_test_performance_with_larger_inputs_in_the_interner_implementation";
        b.iter(|| {
            black_box(interner.intern(black_box(large_str)))
        });
    });

    // Benchmark repeated interning of same string (cache hit)
    group.bench_function("repeated_same_string", |b| {
        interner.intern(b"cached_string"); // Pre-populate
        b.iter(|| {
            black_box(interner.intern(black_box(b"cached_string")))
        });
    });

    // Benchmark many unique strings
    group.bench_function("many_unique_strings", |b| {
        let strings: Vec<Vec<u8>> = (0..1000)
            .map(|i| format!("unique_string_{}", i).into_bytes())
            .collect();

        b.iter(|| {
            for s in &strings {
                black_box(interner.intern(black_box(s.as_slice())));
            }
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_do_intern

);
criterion_main!(benches);