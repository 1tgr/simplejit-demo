use criterion::{criterion_group, criterion_main, Criterion};
use simplejit_demo::ast::IdentId;
use simplejit_demo::{Database, Intern, Result, Source, TargetExt, TypeCk, JIT};
use std::fmt::Write;
use std::mem;

fn compile<DB: JIT + ?Sized>(db: &mut DB, name: IdentId) -> Result<i32> {
    db.reset_module();
    db.cl_ctx(name)?;

    let signature = db.function_signature(name)?;
    let cl_func_id = db.cl_func_id(false, name, signature).unwrap();

    db.with_module_mut(|module| {
        module.finalize_definitions();

        let code = module.get_finalized_function(cl_func_id);
        let code = unsafe { mem::transmute::<*const u8, fn() -> i32>(code) };
        Ok(code())
    })
}

fn bench_noop_change(c: &mut Criterion) {
    let mut db = Database::default();
    let name = db.intern_ident("Main".to_owned());
    let mut counter = 0;

    c.bench_function("noop_change", |b| {
        b.iter(|| {
            db.set_source(format!(
                r"
fn Main() -> i32 {{
    123
}}

fn Other() -> i32 {{
    {}
}}
",
                counter
            ));

            assert_eq!(compile(&mut db, name)?, 123);
            counter += 1;
            Ok(()) as Result<()>
        })
    });
}

fn bench_compile(c: &mut Criterion) {
    let mut db = Database::default();
    let name = db.intern_ident("Main".to_owned());
    let mut counter = 0;

    c.bench_function("compile", |b| {
        b.iter(|| {
            db.set_source(format!(
                r"
fn Main() -> i32 {{
    {}
}}
",
                counter
            ));

            assert_eq!(compile(&mut db, name)?, counter);
            counter += 1;
            Ok(()) as Result<()>
        })
    });
}

fn bench_typeck_big_function(c: &mut Criterion) {
    let mut db = Database::default();
    let name = db.intern_ident("Main".to_owned());
    let mut s = String::new();
    let mut counter = 0;

    c.bench_function("typeck_big_function", |b| {
        b.iter(|| {
            s.clear();
            writeln!(s, "fn Main() -> i32 {{")?;
            writeln!(s, "    A = 0")?;

            for index in counter..counter + 1000 {
                writeln!(s, "    A = A + {}", index)?;
            }

            writeln!(s, "    A")?;
            writeln!(s, "}}")?;

            db.set_source(s.clone());
            db.unify_function(name)?;
            counter += 1;
            Ok(()) as Result<()>
        })
    });
}

criterion_group!(benches, bench_noop_change, bench_compile, bench_typeck_big_function);
criterion_main!(benches);
