use waffle::sexp::{Context, ContextParams, Value};

fn main() {
    let mut p = ContextParams::default();
    p.gc_verbose = 1;

    let mut ctx = Context::new(p);
    ctx.module_search_paths.push("./".to_string());
    ctx.module_search_paths.push(waffle::STDLIB_DIR.to_string());

    let res = ctx.load_file("file.scm", Value::new_null());
    println!("{}", res);
    //ctx.heap().collect();
    ctx.heap().print_stats();
}
