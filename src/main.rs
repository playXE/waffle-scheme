use waffle::{
    sexp::{intern, Context, ContextParams, ContextRef, HashTable, Value},
    vm::{apply, Compiler},
};

const SRC: &'static str = r#"
(define foo 1)
(define bar 2)

"#;

#[inline(never)]
fn foo(ctx: ContextRef) {}

fn main() {
    let mut p = ContextParams::default();
    p.gc_verbose = 0;

    let mut ctx = Context::new(p);
    ctx.module_search_paths.push("./".to_string());
    let res = ctx.load_file("file.scm", Value::new_null());
    println!("{}", res);
}
