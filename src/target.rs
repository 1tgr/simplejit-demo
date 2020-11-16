use cranelift::frontend::FunctionBuilderContext;
use cranelift_simplejit::{SimpleJITBuilder, SimpleJITModule};
use object_pool::Pool;
use std::cell::RefCell;
use std::rc::Rc;

#[salsa::query_group(TargetDatabase)]
pub trait Target {
    #[salsa::input]
    fn module(&self) -> Rc<RefCell<SimpleJITModule>>;

    #[salsa::input]
    fn func_ctx_pool(&self) -> Rc<Pool<FunctionBuilderContext>>;
}

pub trait TargetExt: Target {
    fn reset_module(&mut self) {
        let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
        let module = SimpleJITModule::new(builder);
        self.set_module(Rc::new(RefCell::new(module)));
    }

    fn with_module<T, F: FnOnce(&SimpleJITModule) -> T>(&self, f: F) -> T {
        f(&self.module().borrow())
    }

    fn with_module_mut<T, F: FnOnce(&mut SimpleJITModule) -> T>(&self, f: F) -> T {
        f(&mut self.module().borrow_mut())
    }
}

impl<T: Target + ?Sized> TargetExt for T {}
