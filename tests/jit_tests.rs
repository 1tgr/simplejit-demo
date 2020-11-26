use cranelift::codegen;
use cranelift::codegen::ir::DisplayFunctionAnnotations;
use cranelift_module::{DataContext, Module as _};
use simplejit_demo::{Database, Intern, Lower, Parse, PrettyExt, Result, Source, TargetExt, JIT};
use std::fmt::Write;

fn do_test_pretty(source_text: &str, pretty_text: &str) -> Result<()> {
    let mut db = Database::default();
    db.set_source(source_text.to_owned());

    let function_names = db.function_names()?;

    let mut actual_pretty_text = String::new();
    for name in function_names {
        let function = db.lower_function(name)?;
        let param_names = db.function_param_names(name)?;
        write!(&mut actual_pretty_text, "{}", db.pretty_print_function(name, &function, &param_names))?;
    }

    print!("{}", actual_pretty_text);
    assert_eq!(actual_pretty_text, pretty_text);
    Ok(())
}

fn do_test_ir(source_text: &str, ir: &str) -> Result<()> {
    let mut db = Database::default();
    db.set_source(source_text.to_owned());

    let mut actual_ir = String::new();
    for name in db.function_names()? {
        let ctx = db.cl_ctx(name)?;
        codegen::write_function(&mut actual_ir, &ctx.func, &DisplayFunctionAnnotations::default())?;
    }

    print!("{}", actual_ir);
    assert_eq!(actual_ir, ir);
    Ok(())
}

fn do_test_jit<F>(name: &str, source_text: &str, assert: F) -> Result<()>
where
    F: FnOnce(*const u8),
{
    let mut db = Database::default();
    db.set_source(source_text.to_owned());

    for name in db.function_names()? {
        db.cl_ctx(name)?;
    }

    let name = db.intern_ident(name.to_owned());
    let signature = db.function_signature(name)?;
    let cl_func_id = db.cl_func_id(false, name, signature)?;

    let cl_data_id = db.cl_data_id(db.intern_ident("hello_string".to_owned()))?;
    let mut data_ctx = DataContext::new();
    data_ctx.define(b"hello world!\0".to_vec().into_boxed_slice());

    db.with_module_mut(|module| {
        module.define_data(cl_data_id, &data_ctx)?;
        module.finalize_definitions();

        let code = module.get_finalized_function(cl_func_id);
        assert(code);
        Ok(())
    })
}

macro_rules! jit_test {
    ($id:ident, $name:literal, $assert:expr) => {
        mod $id {
            static SOURCE_TEXT: &str = include_str!(concat!(stringify!($id), ".txt"));
            static PRETTY_TEXT: &str = include_str!(concat!(stringify!($id), "_pretty.txt"));
            static IR_TEXT: &str = include_str!(concat!(stringify!($id), "_ir.txt"));

            #[test]
            fn test_pretty() -> crate::Result<()> {
                super::do_test_pretty(SOURCE_TEXT, PRETTY_TEXT)
            }

            #[test]
            fn test_ir() -> crate::Result<()> {
                super::do_test_ir(SOURCE_TEXT, IR_TEXT)
            }

            #[test]
            fn test_jit() -> crate::Result<()> {
                super::do_test_jit($name, SOURCE_TEXT, $assert)
            }
        }
    };
}

macro_rules! jit_error_test {
    ($id:ident, $name:literal) => {
        mod $id {
            static SOURCE_TEXT: &str = include_str!(concat!(stringify!($id), ".txt"));
            static STDERR_TEXT: &str = include_str!(concat!(stringify!($id), "_stderr.txt"));

            #[test]
            fn test_jit_error() {
                let e = super::do_test_jit($name, SOURCE_TEXT, |_code| {}).expect_err("expected JIT to return an error");
                assert_eq!(e.to_string(), STDERR_TEXT);
            }
        }
    };
}

jit_test!(foo, "Foo", |code| {
    let code = unsafe { std::mem::transmute::<*const u8, fn(isize, isize) -> isize>(code) };
    assert_eq!(code(1, 0), 42);
});

jit_test!(hello, "Say Hello", |code| {
    let code = unsafe { std::mem::transmute::<*const u8, fn() -> isize>(code) };
    code();
});

jit_test!(recursive_fib, "Recursive Fib", |code| {
    let code = unsafe { std::mem::transmute::<*const u8, fn(isize) -> isize>(code) };
    assert_eq!(code(10), 55);
});

jit_test!(iterative_fib, "Iterative Fib", |code| {
    let code = unsafe { std::mem::transmute::<*const u8, fn(isize) -> isize>(code) };
    assert_eq!(code(10), 55);
});

jit_test!(string, "String", |code| {
    let code = unsafe { std::mem::transmute::<*const u8, fn() -> ()>(code) };
    code();
});

jit_error_test!(wrong_variable_type, "Say Hello");
