/// Benchmark to determine the cost of creating multiple tables.
use criterion::{Bencher, Criterion, criterion_group, criterion_main};
use patina_tables::{Field, Tables};

macro_rules! gen_structs {
    ($($name:ident),+) => {
        $(
            impl <T: 'static> Field for $name<T> {}
            #[allow(dead_code)]
            #[derive(Clone, Copy)]
            pub struct $name<T>(T);
        )+
    };
}

gen_structs!(A, B, C, D, E, F);

fn create_1_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_2_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new((A(0u32), B(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_3_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new((A(0u32), B(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_4_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new((A(0u32), B(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32), D(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_5_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new((A(0u32), B(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32), D(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_10_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new(B(0u32));
            tables.insert_new(C(0u32));
            tables.insert_new(D(0u32));
            tables.insert_new(E(0u32));
            tables.insert_new((A(0u32), B(0u32)));
            tables.insert_new((A(0u32), C(0u32)));
            tables.insert_new((A(0u32), D(0u32)));
            tables.insert_new((A(0u32), E(0u32)));
            tables.insert_new((B(0u32), C(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_20_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32));
            tables.insert_new(B(0u32));
            tables.insert_new(C(0u32));
            tables.insert_new(D(0u32));
            tables.insert_new(E(0u32));
            tables.insert_new((A(0u32), B(0u32)));
            tables.insert_new((A(0u32), C(0u32)));
            tables.insert_new((A(0u32), D(0u32)));
            tables.insert_new((A(0u32), E(0u32)));
            tables.insert_new((B(0u32), C(0u32)));
            tables.insert_new((B(0u32), D(0u32)));
            tables.insert_new((B(0u32), E(0u32)));
            tables.insert_new((C(0u32), D(0u32)));
            tables.insert_new((C(0u32), E(0u32)));
            tables.insert_new((D(0u32), E(0u32)));
            tables.insert_new((A(0u32), B(0u32), C(0u32)));
            tables.insert_new((A(0u32), B(0u32), D(0u32)));
            tables.insert_new((A(0u32), B(0u32), E(0u32)));
            tables.insert_new((A(0u32), C(0u32), D(0u32)));
            tables.insert_new((A(0u32), C(0u32), E(0u32)));
        },
        criterion::BatchSize::SmallInput,
    )
}

fn create_50_tables(b: &mut Bencher<'_>) {
    b.iter_batched(
        Tables::new,
        |mut tables| {
            tables.insert_new(A(0u32)); // 1
            tables.insert_new(B(0u32)); // 2
            tables.insert_new(C(0u32)); // 3
            tables.insert_new(D(0u32)); // 4
            tables.insert_new(E(0u32)); // 5
            tables.insert_new(F(0u32)); // 6
            tables.insert_new((A(0u32), B(0u32))); // 7
            tables.insert_new((A(0u32), C(0u32))); // 8
            tables.insert_new((A(0u32), D(0u32))); // 9
            tables.insert_new((A(0u32), E(0u32))); // 10
            tables.insert_new((A(0u32), F(0u32))); // 11
            tables.insert_new((B(0u32), C(0u32))); // 12
            tables.insert_new((B(0u32), D(0u32))); // 13
            tables.insert_new((B(0u32), E(0u32))); // 14
            tables.insert_new((B(0u32), F(0u32))); // 15
            tables.insert_new((C(0u32), D(0u32))); // 16
            tables.insert_new((C(0u32), E(0u32))); // 17
            tables.insert_new((C(0u32), F(0u32))); // 18
            tables.insert_new((D(0u32), E(0u32))); // 19
            tables.insert_new((D(0u32), F(0u32))); // 20
            tables.insert_new((A(0u32), B(0u32), C(0u32))); // 21
            tables.insert_new((A(0u32), B(0u32), D(0u32))); // 22
            tables.insert_new((A(0u32), B(0u32), E(0u32))); // 23
            tables.insert_new((A(0u32), B(0u32), F(0u32))); // 24
            tables.insert_new((A(0u32), C(0u32), D(0u32))); // 25
            tables.insert_new((A(0u32), C(0u32), E(0u32))); // 26
            tables.insert_new((A(0u32), C(0u32), F(0u32))); // 27
            tables.insert_new((A(0u32), D(0u32), E(0u32))); // 28
            tables.insert_new((A(0u32), D(0u32), F(0u32))); // 29
            tables.insert_new((B(0u32), C(0u32), D(0u32))); // 30
            tables.insert_new((B(0u32), C(0u32), E(0u32))); // 31
            tables.insert_new((B(0u32), C(0u32), F(0u32))); // 32
            tables.insert_new((B(0u32), D(0u32), E(0u32))); // 33
            tables.insert_new((B(0u32), D(0u32), F(0u32))); // 34
            tables.insert_new((C(0u32), D(0u32), E(0u32))); // 35
            tables.insert_new((C(0u32), D(0u32), F(0u32))); // 36
            tables.insert_new((C(0u32), E(0u32), F(0u32))); // 37
            tables.insert_new((D(0u32), E(0u32), F(0u32))); // 38
            tables.insert_new((A(0u32), B(0u32), C(0u32), D(0u32))); // 39
            tables.insert_new((A(0u32), B(0u32), C(0u32), E(0u32))); // 40
            tables.insert_new((A(0u32), B(0u32), C(0u32), F(0u32))); // 41
            tables.insert_new((A(0u32), B(0u32), D(0u32), E(0u32))); // 42
            tables.insert_new((A(0u32), B(0u32), D(0u32), F(0u32))); // 43
            tables.insert_new((A(0u32), B(0u32), E(0u32), F(0u32))); // 44
            tables.insert_new((A(0u32), C(0u32), D(0u32), E(0u32))); // 45
            tables.insert_new((A(0u32), C(0u32), D(0u32), F(0u32))); // 46
            tables.insert_new((A(0u32), C(0u32), E(0u32), F(0u32))); // 47
            tables.insert_new((A(0u32), D(0u32), E(0u32), F(0u32))); // 48
            tables.insert_new((B(0u32), C(0u32), D(0u32), E(0u32))); // 49
            tables.insert_new((B(0u32), C(0u32), D(0u32), F(0u32))); // 50
        },
        criterion::BatchSize::SmallInput,
    )
}

pub fn benchmark_create_entity(c: &mut Criterion) {
    let mut group = c.benchmark_group("create_table");

    group.bench_function("create_table_01", create_1_tables);
    group.bench_function("create_table_02", create_2_tables);
    group.bench_function("create_table_03", create_3_tables);
    group.bench_function("create_table_04", create_4_tables);
    group.bench_function("create_table_05", create_5_tables);
    group.bench_function("create_table_10", create_10_tables);
    group.bench_function("create_table_20", create_20_tables);
    group.bench_function("create_table_50", create_50_tables);

    group.finish();
}

criterion_group!(benches, benchmark_create_entity);
criterion_main!(benches);
