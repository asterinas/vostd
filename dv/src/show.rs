use crate::{parser::*, verus::DynError};
use std::result::Result;

pub fn find_struct_in_package(package: &str, r#struct: &str) -> Result<Vec<StructInfo>, DynError> {
    let mut parser = Parser::new(package);
    parser
        .load()
        .register(Rule::rule_process_struct(r#struct))
        .parse();

    if parser.output.is_empty() {
        return Err(format!("No struct definitions found for '{}'", r#struct).into());
    }

    let out: Result<Vec<StructInfo>, String> = parser
        .output
        .iter()
        .map(|item| {
            item.downcast_ref::<StructInfo>()
                .ok_or_else(|| format!("Expected StructInfo, found {:?}", item))
                .cloned()
        })
        .collect();

    Ok(out?)
}
