/// Benchmark to determine the cost of moving an entity between tables when fields are removed or added.
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

gen_structs!(A, B, C, D, E);

fn remove_field<F: 'static + Copy>(b: &mut Bencher<'_>, value: &F) {
    // Add two initial entities to avoid measuring table creation time.
    let setup = || {
        let mut tables = Tables::new();
        let handle = tables.insert_new((A(*value), B(*value)));
        tables.insert_new(A(*value));
        (tables, handle)
    };

    b.iter_batched(
        setup,
        |(mut tables, handle)| {
            tables.remove_fields::<B<F>>(handle);
        },
        criterion::BatchSize::SmallInput,
    );
}

fn add_field<F: 'static + Copy>(b: &mut Bencher<'_>, value: &F) {
    // Add an initial entity to avoid measuring table creation time.
    let setup = || {
        let mut tables = Tables::new();
        let handle = tables.insert_new(A(*value));
        tables.insert_new((A(*value), B(*value)));
        (tables, handle)
    };

    b.iter_batched(
        setup,
        |(mut tables, handle)| {
            tables.add_fields::<B<F>>(handle, B(*value));
        },
        criterion::BatchSize::SmallInput,
    );
}

pub fn benchmark_move_entity(c: &mut Criterion) {
    let mut group = c.benchmark_group("move_handle");

    group.bench_with_input("move_entity_remove_u32", &0u32, remove_field);
    group.bench_with_input("move_entity_remove_u64", &0u64, remove_field);
    group.bench_with_input("move_entity_remove_u128", &0u128, remove_field);

    group.bench_with_input("move_entity_add_u32", &0u32, add_field);
    group.bench_with_input("move_entity_add_u64", &0u64, add_field);
    group.bench_with_input("move_entity_add_u128", &0u128, add_field);

    group.finish();
}

criterion_group!(benches, benchmark_move_entity);
criterion_main!(benches);
