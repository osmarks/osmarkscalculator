use osmarkscalculator::*;
use std::io::BufRead;
use anyhow::Result;

fn main() -> Result<()> {
    let mut ctx = ImperativeCtx::init();
    ctx.eval_program(BUILTINS)?;
    ctx.eval_program(GENERAL_RULES)?;
    ctx.eval_program(FACTOR_DEFINITION)?;
    ctx.eval_program(DENORMALIZATION_RULES)?;
    ctx.eval_program(NORMALIZATION_RULES)?;
    ctx.eval_program(DIFFERENTIATION_DEFINITION)?;
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        let line = line?;
        match ctx.eval_program(&line) {
            Ok(Some(result)) => println!("{}", result.render_to_string(&ctx.base_env)),
            Ok(None) => (),
            Err(e) => println!("Error: {:?}", e)
        }
    }
    Ok(())
}