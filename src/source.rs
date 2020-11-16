#[salsa::query_group(SourceDatabase)]
pub trait Source {
    #[salsa::input]
    fn source(&self) -> String;
}
