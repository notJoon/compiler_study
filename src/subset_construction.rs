use std::collections::{BTreeSet, HashMap, VecDeque};

type State = usize;
type Symbol = char;
type TransitionTable = HashMap<(State, Option<Symbol>), BTreeSet<State>>;

/// Calculate the epsilon closure of a state in an NFA.
///
/// The epsilon closure of a state is the set of NFA states reachable from the given state,
/// including the state itself, by traveling along edges that are labeled with the epsilon (ε)
/// symbol, which represents a transition that does not consume any input symbols.
///
/// # Arguments
///
/// * `state` - The state for which the epsilon closure is to be calculated.
/// * `transitions` - A reference to the NFA's transition table which contains mappings
/// from state-symbol pairs to sets of destination states.
///
/// # Returns
///
/// A set of states that are in the epsilon closure of the given state.
fn epsilon_closure(state: State, transitions: &TransitionTable) -> BTreeSet<State> {
    let mut closure = BTreeSet::new();
    let mut stack = vec![state];

    while let Some(s) = stack.pop() {
        closure.insert(s);

        if let Some(next_states) = transitions.get(&(s, None)) {
            for &next_state in next_states {
                if !closure.contains(&next_state) {
                    stack.push(next_state);
                }
            }
        }
    }

    closure
}

/// Perform the subset construction algorithm to convert an NFA to a DFA.
///
/// This algorithm constructs a DFA that is equivalent to an NFA by creating states
/// in the DFA that correspond to sets of NFA states. The DFA will then have transitions
/// for each symbol in the alphabet that lead to new sets of NFA states, constructed based
/// on the epsilon closure of the states reachable by that symbol from the current set.
///
/// # Arguments
///
/// * `start_state` - The start state of the NFA.
/// * `transitions` - A reference to the NFA's transition table.
/// * `alphabet` - A slice containing the input alphabet symbols for the NFA.
///
/// # Returns
///
/// A tuple containing a vector of DFA states (each represented as a set of NFA states)
/// and the DFA transition table.
fn subset_construction(
    start_state: State,
    transitions: &TransitionTable,
    alphabet: &[Symbol],
) -> (Vec<BTreeSet<State>>, TransitionTable) {
    let mut dfa_states = vec![epsilon_closure(start_state, transitions)];
    let mut dfa_transitions = TransitionTable::new();
    let mut unmarked_states = VecDeque::new();
    unmarked_states.push_back(dfa_states[0].clone());

    while let Some(d_states) = unmarked_states.pop_front() {
        for &a in alphabet {
            let u = get_next_states(&d_states, &a, transitions);

            if !u.is_empty() {
                let _u_index = if let Some(pos) = dfa_states.iter().position(|s| *s == u) {
                    pos
                } else {
                    dfa_states.push(u.clone());
                    unmarked_states.push_back(u.clone());
                    dfa_states.len() - 1
                };

                dfa_transitions.insert(
                    (
                        dfa_states.iter().position(|s| *s == d_states).unwrap(),
                        Some(a),
                    ),
                    u,
                );
            }
        }
    }

    (dfa_states, dfa_transitions)
}

fn get_next_states(
    d_start: &BTreeSet<State>,
    a: &Symbol,
    transitions: &TransitionTable,
) -> BTreeSet<State> {
    let mut u = BTreeSet::new();

    for &n in d_start {
        if let Some(next_states) = transitions.get(&(n, Some(*a))) {
            for &next_state in next_states {
                u.insert(next_state);
            }
        }
    }

    u
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_state_nfa() {
        let transitions = TransitionTable::new(); // No transitions
        let alphabet = vec![];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        assert_eq!(dfa_states.len(), 1);
        assert!(dfa_transitions.is_empty());
    }

    #[test]
    fn test_nfa_with_epsilon_transitions() {
        let mut transitions = TransitionTable::new();
        transitions.insert((0, None), vec![1].into_iter().collect());
        transitions.insert((1, None), vec![2].into_iter().collect());
        let alphabet = vec![];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        // Epsilon transitions lead to a single DFA state
        assert_eq!(dfa_states.len(), 1);
        assert!(dfa_transitions.is_empty());
    }

    #[test]
    fn test_nfa_one_symbol_no_epsilon() {
        let mut transitions = TransitionTable::new();
        transitions.insert((0, Some('a')), vec![1].into_iter().collect());
        let alphabet = vec!['a'];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        assert_eq!(dfa_states.len(), 2);
        assert_eq!(dfa_transitions.len(), 1);
        assert!(dfa_transitions.contains_key(&(0, Some('a'))));
    }

    #[test]
    fn test_nfa_multiple_transitions() {
        let mut transitions = TransitionTable::new();
        transitions.insert((0, Some('a')), vec![1, 2].into_iter().collect());
        transitions.insert((1, Some('b')), vec![0].into_iter().collect());
        transitions.insert((2, Some('a')), vec![2].into_iter().collect());

        let alphabet = vec!['a', 'b'];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        assert!(dfa_states.len() > 2);
        assert!(dfa_transitions.len() > 1);
    }

    #[test]
    fn test_nfa_with_epsilon_and_symbols() {
        let mut transitions = TransitionTable::new();
        transitions.insert((0, None), vec![1].into_iter().collect());
        transitions.insert((0, Some('a')), vec![0].into_iter().collect());
        transitions.insert((1, Some('b')), vec![2].into_iter().collect());
        transitions.insert((2, Some('a')), vec![1].into_iter().collect());
        let alphabet = vec!['a', 'b'];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        assert!(dfa_states.len() >= 3);
        assert!(dfa_transitions.len() >= 2);
    }

    #[test]
    fn test_nfa_with_overlapping_epsilon_closures() {
        let mut transitions = TransitionTable::new();
        transitions.insert((0, None), vec![1].into_iter().collect());
        transitions.insert((1, None), vec![2].into_iter().collect());
        transitions.insert((0, Some('a')), vec![0, 1].into_iter().collect());
        transitions.insert((1, Some('b')), vec![2].into_iter().collect());
        transitions.insert((2, Some('a')), vec![1].into_iter().collect());
        println!("{:?}", transitions);
        let alphabet = vec!['a', 'b'];
        let start_state = 0;

        let (dfa_states, dfa_transitions) =
            subset_construction(start_state, &transitions, &alphabet);

        assert!(dfa_states.len() >= 3);
        assert!(dfa_transitions.len() >= 2);
    }
}
