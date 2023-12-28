use std::collections::{BTreeSet, HashMap, HashSet};

mod dfa_minimization;
mod subset_construction;

pub type State = usize;
pub type Symbol = char;
pub type HopcraftTransitionTable = HashMap<(State, Option<Symbol>), BTreeSet<State>>;
pub type Partition = HashSet<BTreeSet<State>>;
