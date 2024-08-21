use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
    usize,
};

use crate::symbols::{self, Symbol};
use crate::{one_or_more::OneOrMore, symbols::SymbolsRegistry};

use log::debug;

/// This module implements the core types to be
/// used to build a parser generator engine based in a BNF grammar.
///
/// We drop the names of the productions rules and terminals
/// and instead we use [usize]. The current lower bound for
/// target_pointer_width is 16, this means we can represent
/// at least 65536 different symbols, enough for most grammars.

/// A production is of the form
/// symbol1 : symbol2 symbol3 symbol4
/// We identify it's parts as :
/// ```
/// Production{name:Id(1),values:(Id(2),vec![Id(3),Id(4)])}
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Production {
    /// The use of [IdType] in the field [Production::name] in this
    /// definition guaranties that we can't correctly assign rules
    /// to [Symbol::Eof] and [Symbol::Empty].
    name: usize,
    /// The explicit [OneOrMore] here guaranties that the
    /// productions are nullable iff it's symbols
    /// are all nullable, and not by having empty productions.
    values: OneOrMore<Symbol>,
}

impl Production {
    pub fn from_vector(
        name: usize,
        raw_name: &String,
        raw_production: Vec<Symbol>,
    ) -> Result<Self, GrammarError> {
        match OneOrMore::make_option(raw_production) {
            Some(values) => Ok(Production { name, values }),
            None => Err(GrammarError::EmptyProduction(raw_name.clone())),
        }
    }

    pub fn readable(&self, table: &SymbolsRegistry) -> Option<String> {
        let name = table.solve_id(self.name)?;
        let productions: Vec<&str> = self
            .values
            .iter()
            .map(|symbol| table.solve_symbol(*symbol))
            .collect::<Option<Vec<_>>>()?
            .iter()
            .map(|s| s.as_str())
            .collect();
        let rendered_production = productions.join(" ");
        Some(format!("{} : {}", name, rendered_production))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Rule {
    /// This also help us with the guaranties that a
    /// [Symbol] is nullable iff it has at least one
    /// explicit production with at least one element
    /// and all it's components are nullable.
    productions: OneOrMore<Production>,
}

impl Rule {
    pub fn from_vector(
        name: usize,
        raw_name: &String,
        raw_rule: Vec<Vec<Symbol>>,
    ) -> Result<Self, GrammarError> {
        let mut productions: Vec<Production> =
            Vec::with_capacity(raw_rule.len());
        let mut errors: Vec<GrammarError> = vec![];
        for raw_production in raw_rule {
            match Production::from_vector(name, raw_name, raw_production) {
                Ok(production) => productions.push(production),
                Err(x) => errors.push(x),
            }
        }
        match OneOrMore::make_option(productions) {
            None => {
                let last_error = GrammarError::EmptyRule(raw_name.clone());
                if errors.len() == 0 {
                    Err(last_error)
                } else {
                    errors.push(last_error);
                    Err(GrammarError::MultipleErrors(errors))
                }
            }
            Some(rule_inner) => {
                if errors.len() == 0 {
                    Ok(Rule {
                        productions: rule_inner,
                    })
                } else if errors.len() == 1 {
                    Err(errors.remove(0))
                } else {
                    Err(GrammarError::MultipleErrors(errors))
                }
            }
        }
    }

    pub fn readable(&self, table: &SymbolsRegistry) -> Option<String> {
        let acc: Vec<String> = self
            .productions
            .iter()
            .map(|i| i.readable(table))
            .collect::<Option<Vec<_>>>()?;
        Some(acc.join(";\n"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grammar {
    /// A [Symbol::Id] maps directly to element of this
    /// vector [Grammar::rules] if they are non terminals,
    /// otherwise they are terminals.
    rules: Vec<Rule>,
    len: usize,
    registry: SymbolsRegistry,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum GrammarError {
    MultipleErrors(Vec<GrammarError>),
    EmptyProduction(String),
    EmptyRule(String),
}

impl Grammar {
    #[inline]
    pub fn get_rule(&self, i: usize) -> Option<&Rule> {
        self.rules.get(i)
    }

    #[inline]
    pub fn transitive_closure<T>(
        &self,
        new: fn() -> T,
        step: fn(&mut T, &Grammar) -> bool,
    ) -> T {
        let mut arg = new();
        loop {
            if !step(&mut arg, self) {
                break;
            }
        }
        arg
    }

    pub fn from_table(
        raw_grammar: &HashMap<String, Vec<Vec<String>>>,
    ) -> Result<Grammar, GrammarError> {
        let (registry, raw_rules) = SymbolsRegistry::make(raw_grammar);
        let mut rules: Vec<Rule> = Vec::new();
        let mut errors: Vec<GrammarError> = Vec::new();
        for (name, raw_rule) in raw_rules.into_iter().enumerate() {
            match registry.solve_id(name) {
                Some(raw_name) => {
                    match Rule::from_vector(name, raw_name, raw_rule) {
                        Ok(rule) => rules.push(rule),
                        Err(e) => errors.push(e),
                    }
                }
                None => continue,
            }
        }
        if errors.len() == 0 {
            let len = rules.len();
            Ok(Grammar {
                rules,
                len,
                registry,
            })
        } else if errors.len() == 1 {
            Err(errors.remove(0))
        } else {
            Err(GrammarError::MultipleErrors(errors))
        }
    }

    pub fn from_vector(
        raw_grammar: Vec<(&str, Vec<Vec<&str>>)>,
    ) -> Result<Grammar, GrammarError> {
        let mut dic = HashMap::new();
        for (name, productions) in raw_grammar.into_iter() {
            let new_name = String::from(name);
            let mut rule = Vec::new();
            for production in productions {
                let new_production: Vec<String> = production
                    .into_iter()
                    .map(|name2: &str| String::from(name2))
                    .collect();
                rule.push(new_production);
            }
            dic.insert(new_name, rule);
        }
        Grammar::from_table(&dic)
    }

    pub fn readable(&self) -> Option<String> {
        let acc: Vec<String> = self
            .rules
            .iter()
            .map(|i| i.readable(&self.registry))
            .collect::<Option<Vec<_>>>()?;
        Some(acc.join("\n"))
    }

    #[inline]
    pub fn is_terminal(&self, name: &Symbol) -> bool {
        match *name {
            Symbol::Id(x) => (self.len) <= x,
            _ => true,
        }
    }

    pub fn solve_name(&self, name: &String) -> Option<Symbol> {
        self.registry.solve_name(name)
    }

    pub fn solve_id(&self, name_id: usize) -> Option<&String> {
        self.registry.solve_id(name_id)
    }

    pub fn solve_symbol(&self, symbol: Symbol) -> Option<&String> {
        self.registry.solve_symbol(symbol)
    }

    pub fn solve_symbols<'a, T: Iterator<Item = &'a Symbol>>(
        &'a self,
        symbols: T,
    ) -> impl Iterator<Item = Option<&'a String>> {
        symbols.into_iter().map(|&x| self.solve_symbol(x))
    }

    pub fn solve_ids<'a, T: Iterator<Item = usize>>(
        &'a self,
        symbols: T,
    ) -> impl Iterator<Item = Option<&'a String>> {
        symbols.into_iter().map(|x| self.solve_id(x))
    }

    pub fn solve_names<'a, T: Iterator<Item = &'a String> + 'a>(
        &'a self,
        symbols: T,
    ) -> impl Iterator<Item = Option<Symbol>> + 'a {
        symbols.into_iter().map(|x| self.solve_name(x))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NullableSets {
    sets: HashSet<Symbol>,
}

impl NullableSets {
    pub fn readable<'a>(
        &'a self,
        grammar: &'a Grammar,
    ) -> Option<HashSet<&'a String>> {
        grammar.solve_symbols(self.sets.iter()).collect()
    }
}

/// The computed First Sets for every non terminal
/// in a [Grammar], that's why [new] require
/// a [Grammar].
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FirstSets {
    sets: Vec<HashSet<Symbol>>,
}

impl FirstSets {
    pub fn new(grammar: &Grammar) -> Self {
        let v = (0usize..(grammar.len)).map(|_| HashSet::new()).collect();
        FirstSets { sets: v }
    }

    pub fn into_hash_set(&self) -> HashMap<Symbol, HashSet<Symbol>> {
        self.sets
            .iter()
            .enumerate()
            .map(|(name_id, hash_set)| {
                let symbol = Symbol::Id(name_id);
                (symbol, hash_set.clone())
            })
            .collect()
    }

    pub fn readable<'a>(
        &'a self,
        grammar: &'a Grammar,
    ) -> Option<HashMap<&'a String, HashSet<&'a String>>> {
        self.sets
            .iter()
            .enumerate()
            .map(|(name, set)| {
                let new_name: &String = grammar.solve_id(name)?;
                let new_set: HashSet<&'a String> =
                    grammar.solve_symbols(set.iter()).collect::<Option<_>>()?;
                Some((new_name, new_set))
            })
            .collect()
    }
}

impl Into<HashMap<Symbol, HashSet<Symbol>>> for FirstSets {
    fn into(self) -> HashMap<Symbol, HashSet<Symbol>> {
        self.into_hash_set()
    }
}

/// The returned bool is used to know if we
/// mutated the set.
pub fn compute_nullables_step(
    nullables: &mut HashSet<Symbol>,
    grammar: &Grammar,
) -> bool {
    let mut flag = false;
    for (index, rule) in grammar.rules.iter().enumerate() {
        if nullables.contains(&Symbol::Id(index)) {
            continue;
        }
        for production in rule.productions.iter() {
            let mut all_are_nullable = true;
            for item in production.values.iter() {
                if (grammar.is_terminal(item) && item.is_empty())
                    || nullables.contains(item)
                {
                    continue;
                } else {
                    all_are_nullable = false;
                    break;
                }
            }
            if all_are_nullable {
                flag = true;
                nullables.insert(Symbol::Id(production.name));
                break;
            }
        }
    }
    flag
}

/// The [Symbol::Empty] is always included.
pub fn compute_nullables(grammar: &Grammar) -> NullableSets {
    let sets = grammar.transitive_closure(
        || HashSet::from([Symbol::Empty]),
        compute_nullables_step,
    );
    NullableSets { sets }
}

/// First sets algorithm :
/// - Create a collection storing empty sets for every not terminal
/// - Iterate over all the rules on the grammar,
/// - for a rule `a : b c d f g` we add the current value of First[b] to a,
///  the if b can produce the empty word (is nullable) also add
///  the First[c], repeat for c d f g until we found one of them
///  not nullable or we get out of items.
///  - First[Terminal] = {Terminal} ever!
///  - Repeat until the process don't add new elements to any First set.
/// We use the return to know if we mutated the First sets in this call.
/// if we didn't, we got to the end of the algorithm.
pub fn compute_first_sets_step(
    sets: &mut Vec<Rc<RefCell<HashSet<Symbol>>>>,
    nullables: &NullableSets,
    grammar: &Grammar,
) -> bool {
    // This tell us if we mutated [sets]
    let mut flag = false;
    debug!(
        "initial state : sets = {:?},  nullables = {:?}",
        sets.iter()
            .enumerate()
            .map(|(index, x)| {
                let set = (*x.borrow())
                    .iter()
                    .map(|&y| grammar.solve_symbol(y))
                    .collect::<Option<HashSet<_>>>()?;
                let name = grammar.registry.solve_id(index)?;
                Some((name, set))
            })
            .collect::<Option<HashMap<_, _>>>(),
        nullables.readable(grammar),
    );
    debug!("{:}", grammar.readable().expect("gramar.readable error"));
    for (index, rule) in grammar.rules.iter().enumerate() {
        debug!(
            "loop principal: sets = {:?},  nullables = {:?}, index = {:?}",
            sets.iter()
                .enumerate()
                .map(|(index, x)| {
                    let set = (*x.borrow())
                        .iter()
                        .map(|&y| grammar.solve_symbol(y))
                        .collect::<Option<HashSet<_>>>()?;
                    let name = grammar.registry.solve_id(index)?;
                    Some((name, set))
                })
                .collect::<Option<HashMap<_, _>>>(),
            nullables.readable(grammar),
            index
        );
        let current_firsts = unsafe { sets.get_unchecked(index).clone() };
        for production in rule.productions.iter() {
            let mut last_item_nullable = false;
            for item in production.values.iter() {
                last_item_nullable = false;
                let item_firsts: &HashSet<Symbol> = match *item {
                    Symbol::Id(item_id) => unsafe {
                        debug!(
                            " adding first sets of item_id: {:?}",
                            grammar.solve_id(item_id)
                        );
                        if grammar.is_terminal(item) {
                            if item.is_empty() {
                                &HashSet::new()
                            } else {
                                &HashSet::from([*item])
                            }
                        } else {
                            &(sets.get_unchecked(item_id).borrow())
                        }
                    },
                    _ => &HashSet::from([*item]),
                };
                let difference = &(item_firsts
                    - &(*current_firsts.clone().borrow()))
                    - &HashSet::from([Symbol::Empty]);
                if !difference.is_empty() {
                    flag = true;
                    let mut current_firsts_mut =
                        (&*current_firsts).borrow_mut();
                    current_firsts_mut.extend(difference);
                }
                if !nullables.sets.contains(item) {
                    break;
                }
                debug!("was nullable!");
                last_item_nullable = true;
            }
            if last_item_nullable {
                let mut current_firsts_mut = (&*current_firsts).borrow_mut();
                current_firsts_mut.insert(Symbol::Empty);
            }
        }
        debug!("setting set at {index} with {current_firsts:?}");
        sets[index] = current_firsts;
    }
    flag
}

pub fn compute_first_sets(
    nullables: &NullableSets,
    grammar: &Grammar,
) -> FirstSets {
    let mut arg: Vec<_> = (0usize..(grammar.len))
        .map(|_| Rc::new(RefCell::new(HashSet::new())))
        .collect();
    loop {
        if !compute_first_sets_step(&mut arg, nullables, grammar) {
            break;
        }
    }
    let out = arg
        .into_iter()
        .map(|value| (*value).borrow().clone())
        .collect();
    FirstSets { sets: out }
}

macro_rules! make_grammar {
    ($($key:literal : $($($item:literal)+)|+),+) => {

        {
            let v : Vec<(&str,Vec<Vec<&str>>)> = vec![$( ($key, vec![$( vec![$( $item, )+], )+]),  )+];
            Grammar::from_vector(v)
        }

    };
}

pub mod test_grammars {
    use super::*;
    use std::sync::LazyLock;
    pub static EMPTY_GRAMMAR: LazyLock<Grammar> = LazyLock::new(|| {
        Grammar::from_vector(vec![]).expect("can't create grammar!")
    });

    pub static EMPTY_PRODUCTION_GRAMMAR: LazyLock<Grammar> =
        LazyLock::new(|| {
            make_grammar! {
                "s" : "a" "b" | "c",
                "a" : "A" | "Empty",
                "b" : "B" | "Empty",
                "c" : "C",
                "d" : "a" "c" | "c"
            }
            .expect("can't create grammar!")
        });

    pub static MATH_GRAMMAR: LazyLock<Grammar> = LazyLock::new(|| {
        make_grammar! {
            "expr" : "expr" "Plus" "factor" | "expr" "Minus" "factor" | "factor"
            ,"factor" : "atom" "Star" "atom" | "atom" "Div" "atom" | "atom"
            ,"atom" : "Nat" | "LParen" "atom" "RParen"
        }
        .expect("can't create grammar!")
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use paste::paste;
    use test_grammars::*;

    use simple_logger::SimpleLogger;
    use std::sync::Once;

    static INIT_LOG: Once = Once::new();

    fn setup_log() {
        INIT_LOG.call_once(|| SimpleLogger::new().init().unwrap());
    }

    pub fn first_sets_from_vec<'a>(
        v: Vec<(&'a str, Vec<&'a str>)>,
    ) -> HashMap<String, HashSet<String>> {
        v.into_iter()
            .map(|(name, name_dic)| {
                let new_name = String::from(name);
                let hash_dic =
                    name_dic.into_iter().map(|x| String::from(x)).collect();
                (new_name, hash_dic)
            })
            .collect::<HashMap<String, HashSet<String>>>()
    }

    macro_rules! make_first_sets {
        ($($name:literal : $($item:literal)* ),*) => {
            {
                vec![$( ($name,vec![$($item,)*]), )*]
            }
        };
    }

    macro_rules! make_nullable_test {
        ($name:tt, $raw_grammar:expr, $raw_nulls:expr)=> {
            paste! {

            #[test]
            fn [< test_nullable_ $name >](){
                setup_log();
                let grammar = Grammar::from_vector($raw_grammar).expect("can't create grammar!");
                let expected = NullableSets{sets:grammar.registry.make_set($raw_nulls).expect("can't create expected set")};
                let nullables = compute_nullables(&grammar);
                assert!(
                    nullables == expected,
                    "nullables = {:?}, expected = {:?}",
                    nullables.readable(&grammar),
                    expected.readable(&grammar),
                )
                }
            }
        }
    }

    macro_rules! make_test_from_static {
        ($name:tt, $static_name:tt, $raw_nulls:expr,$raw_first:expr) => {
            paste! {

            #[test]
            fn [< test_ $name >](){
                setup_log();
                let grammar = &*$static_name;
                let expected_nullables = NullableSets{sets:grammar.registry.make_set($raw_nulls).expect("can't create expected set")};
                let nullables = compute_nullables(&grammar);
                assert!(
                    nullables == expected_nullables,
                    "nullables = {:?}, expected = {:?}",
                    nullables.readable(&grammar),
                    expected_nullables.readable(&grammar),
                );
                let first_sets_as_hash = compute_first_sets(&nullables, grammar).readable(grammar).expect("can't create first set");
                let expected_firsts = first_sets_from_vec($raw_first);
                assert!(
                    first_sets_as_hash == expected_firsts,
                    "first_sets_as_hash = {:?}, expected = {:?}",
                    first_sets_as_hash,
                    expected_firsts
                )

                }
            }
        };
    }

    make_test_from_static!(
        empty_grammar,
        EMPTY_GRAMMAR,
        vec!["Empty",],
        make_first_sets![]
    );

    make_nullable_test!(
        single_rule,
        vec![("one_rule", vec![vec!["Empty"], vec!["none"]])],
        vec!["Empty", "one_rule"]
    );

    // sep_by1 : Uint ("," Uint)* ","?
    // TODO: Maybe add
    // sep_by1 : (Uint ",")* Uint ","?
    // to and compare both imputs
    make_nullable_test!(
        sep_by1_with_maybe,
        vec![
            (
                "sep_by1",
                vec![vec!["Uint", "maybe_separator", "maybe_comma"]]
            ),
            ("maybe_comma", vec![vec!["Comma"], vec!["Empty"]]),
            (
                "maybe_separator",
                vec![vec!["Comma", "Uint"], vec!["Empty"]]
            )
        ],
        vec!["Empty", "maybe_comma", "maybe_separator"]
    );

    make_test_from_static!(
        math_grammar,
        MATH_GRAMMAR,
        vec!["Empty"],
        make_first_sets!["expr": "LParen" "Nat", "factor": "LParen" "Nat","atom":"LParen" "Nat"]
    );

    make_test_from_static!(
        empty_produciton_grammar,
        EMPTY_PRODUCTION_GRAMMAR,
        vec!["s", "a", "b", "Empty"],
        make_first_sets!["s": "A" "B" "C" "Empty", "a": "Empty" "A", "b":"B" "Empty", "c":"C", "d":"A" "E"]
    );
}
