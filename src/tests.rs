use crate::{Database, Intern, Jit, Result, Source, TargetExt, TypeCk};
use std::mem;

fn compile<DB: Jit + ?Sized>(db: &mut DB) -> Result<i32> {
    let name = db.intern_ident("Main".to_owned());
    assert_eq!(db.function_names().unwrap(), vec![name]);

    db.reset_module();
    db.clif_ctx(name)?;

    let signature = db.function_signature(name)?;
    let clif_func_id = db.clif_func_id(false, name, signature).unwrap();

    db.with_module_mut(|module| {
        module.finalize_definitions();

        let code = module.get_finalized_function(clif_func_id);
        let code = unsafe { mem::transmute::<*const u8, fn() -> i32>(code) };
        Ok(code())
    })
}

fn compile_error<DB: Jit + ?Sized>(db: &mut DB, text: &str) {
    assert_eq!(compile(db).expect_err("expected compilation error").to_string(), text);
}

#[test]
fn test_source_update() -> Result<()> {
    let mut db = Database::default();

    {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
123
}
",
        ));
        assert_eq!(compile(&mut db)?, 123);
    }

    {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
broken
}
",
        ));
        compile_error(&mut db, "reading from undeclared variable broken");
    }

    {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
A = 1
A = A == 1
}
",
        ));
        compile_error(&mut db, "can't unify i32 with bool");
    }

    {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
12 * 10 + 4
}
",
        ));
        assert_eq!(compile(&mut db)?, 124);
    }

    Ok(())
}

#[test]
fn test_noop_update() -> Result<()> {
    let mut db = Database::default();
    let name = db.intern_ident("Main".to_owned());

    let func1 = {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
123
}
",
        ));

        db.unify_function(name)?
    };

    let func2 = {
        db.set_source(String::from(
            r"
fn Main() -> i32 {
            123
}

fn Zzz() -> i32 {
broken
}
",
        ));

        db.unify_function(name)?
    };

    assert_eq!(func1, func2);
    Ok(())
}
