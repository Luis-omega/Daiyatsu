use crate::grammar::Production;

#[derive(Debug)]
pub struct Item<'production> {
    pub production: &'production Production,
    pub position: u16,
}
