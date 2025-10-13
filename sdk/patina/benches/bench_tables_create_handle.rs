/// Benchmark to determine the cost of creating a single table with various number of fields and sizes.
use criterion::{Bencher, Criterion, criterion_group, criterion_main};
use patina_tables::{Field, Fields, Tables};

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

gen_structs!(A, B, C, D, E);

fn create_entity_with_fields<F>(b: &mut Bencher<'_>, fields: &F)
where
    F: Fields + Copy,
{
    // Add a initial entity to avoid measuring table creation time.
    let setup = || {
        let mut tables = Tables::new();
        tables.insert_new(*fields);
        tables
    };

    b.iter_batched(
        setup,
        |mut tables| {
            tables.insert_new(*fields);
        },
        criterion::BatchSize::SmallInput,
    );
}

pub fn benchmark_create_entity(c: &mut Criterion) {
    let mut group = c.benchmark_group("create_handle");

    group.bench_with_input("create_handle_1_u32", &A(0u32), create_entity_with_fields);
    group.bench_with_input("create_handle_1_u64", &A(0u64), create_entity_with_fields);
    group.bench_with_input("create_handle_1_u128", &A(0u128), create_entity_with_fields);

    group.bench_with_input(
        "create_handle_2_u32",
        &(A(0u32), B(0u32)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_2_u64",
        &(A(0u64), B(0u64)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_2_u128",
        &(A(0u128), B(0u128)),
        create_entity_with_fields,
    );

    group.bench_with_input(
        "create_handle_3_u32",
        &(A(0u32), B(0u32), C(0u32)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_3_u64",
        &(A(0u64), B(0u64), C(0u64)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_3_u128",
        &(A(0u128), B(0u128), C(0u128)),
        create_entity_with_fields,
    );

    group.bench_with_input(
        "create_handle_4_u32",
        &(A(0u32), B(0u32), C(0u32), D(0u32)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_4_u64",
        &(A(0u64), B(0u64), C(0u64), D(0u64)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_4_u128",
        &(A(0u128), B(0u128), C(0u128), D(0u128)),
        create_entity_with_fields,
    );

    group.bench_with_input(
        "create_handle_5_u32",
        &(A(0u32), B(0u32), C(0u32), D(0u32), E(0u32)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_5_u64",
        &(A(0u64), B(0u64), C(0u64), D(0u64), E(0u64)),
        create_entity_with_fields,
    );
    group.bench_with_input(
        "create_handle_5_u128",
        &(A(0u128), B(0u128), C(0u128), D(0u128), E(0u128)),
        create_entity_with_fields,
    );

    group.finish();
}

criterion_group!(benches, benchmark_create_entity);
criterion_main!(benches);
