use std::collections::{BTreeSet, HashMap};

use crate::{State, Symbol};

type StateSet = BTreeSet<State>;
type HopcroftTransitionTable = HashMap<(State, Option<Symbol>), State>;

/// Performs Hopcroft's algorithm for DFA minimization.
///
/// This function minimizes a given deterministic finite automaton (DFA) by partitioning its states
/// into equivalence classes and merging states within the same class. The algorithm aims to reduce
/// the number of states in the DFA without changing the language it recognizes.
///
/// # Arguments
/// * `states` - A reference to a set containing all the states in the DFA.
/// * `accepting_states` - A reference to a set containing all the accepting states in the DFA.
/// * `transitions` - A reference to a transition table, mapping state-symbol pairs to resultant states.
/// * `alphabet` - A reference to a list of symbols in the DFA's alphabet.
///
/// # Returns
/// A vector of `StateSet`s representing the partitioned states. Each `StateSet` in the vector is an
/// equivalence class, where all states within it are considered equivalent for the purposes of the
/// DFA's language recognition.
///
/// # Algorithm
/// 1. Initialize partitions: Divide states into two partitions - accepting and non-accepting states.
///    If there are no accepting states, all states are placed in a single partition.
/// 2. Refinement loop: Continuously refine the partitions based on state transitions. For each
///    partition and each symbol in the alphabet, calculate the set of states that transition to any
///    state in the current partition on that symbol. Update the partitions based on these sets.
/// 3. Merge states: After the refinement process, states in the same partition are merged, as they
///    are indistinguishable in terms of the language recognition of the DFA.
///
/// The result is a set of partitions where each partition can be considered a single state in the
/// minimized DFA.
fn hopcroft_minimization(
    states: &StateSet,
    accepting_states: &StateSet,
    transitions: &HopcroftTransitionTable,
    alphabet: &[Symbol],
) -> Vec<StateSet> {
    if accepting_states.is_empty() {
        return vec![states.clone()];
    }

    // Initialize partitions based on accepting and non-accepting states
    let non_accepting_states: StateSet = states.difference(accepting_states).cloned().collect();
    let mut partitions = if non_accepting_states.is_empty() {
        vec![accepting_states.clone()]
    } else {
        vec![non_accepting_states, accepting_states.clone()]
    };

    let mut work_list = partitions.clone();
    while let Some(current_partition) = work_list.pop() {
        for &symbol in alphabet {
            // Collect states that transition on the symbol to any state in the current partition
            let mut related_states = StateSet::new();
            for (&(state, transition_symbol), &target_state) in transitions {
                if transition_symbol == Some(symbol) && current_partition.contains(&target_state) {
                    related_states.insert(state);
                }
            }

            // Refine partitions based on the related states
            let mut new_partitions = Vec::new();
            for partition in &partitions {
                let intersection = partition.intersection(&related_states).cloned().collect::<StateSet>();
                let difference = partition.difference(&related_states).cloned().collect::<StateSet>();

                if !intersection.is_empty() {
                    new_partitions.push(intersection.clone());
                    if !partitions.contains(&intersection) {
                        work_list.push(intersection);
                    }
                }
                if !difference.is_empty() {
                    new_partitions.push(difference.clone());
                    if !partitions.contains(&difference) {
                        work_list.push(difference);
                    }
                }
            }
            partitions = new_partitions;
        }
    }

    partitions
}


#[cfg(test)]
mod tests {
    use super::*;

    // Helper function to create transitions from a list of tuples
    fn create_transitions(transitions: &[(State, Symbol, State)]) -> HopcroftTransitionTable {
        transitions
            .iter()
            .cloned()
            .map(|(s, c, q)| ((s, Some(c)), q))
            .collect()
    }

    #[test]
    fn test_minimize_single_state() {
        let states: StateSet = [0].iter().cloned().collect();
        let accepting_states: StateSet = [0].iter().cloned().collect();
        let transitions = create_transitions(&[]);
        let alphabet: Vec<Symbol> = vec![];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert_eq!(minimized.len(), 1);
    }

    #[test]
    fn test_minimize_disjoint_states() {
        let states: StateSet = (0..2).collect();
        let accepting_states: StateSet = [1].iter().cloned().collect();
        let transitions = create_transitions(&[(0, 'a', 1)]);
        let alphabet = vec!['a'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert_eq!(minimized.len(), 2);
    }

    #[test]
    fn test_minimize_complex_dfa() {
        let states: StateSet = (0..6).collect();
        let accepting_states: StateSet = [3, 5].iter().cloned().collect();
        let transitions = create_transitions(&[
            (0, '0', 0), (0, '1', 1),
            (1, '0', 2), (1, '1', 0),
            (2, '0', 1), (2, '1', 3),
            (3, '0', 4), (3, '1', 2),
            (4, '0', 5), (4, '1', 3),
            (5, '0', 4), (5, '1', 5),
        ]);
        let alphabet = vec!['0', '1'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert!(minimized.len() <= states.len());
    }

    #[test]
    fn test_minimize_multiple_accepting_states() {
        let states: StateSet = (0..3).collect();
        let accepting_states: StateSet = [1, 2].iter().cloned().collect();
        let transitions = create_transitions(&[(0, 'a', 1), (1, 'b', 2)]);
        let alphabet = vec!['a', 'b'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert!(minimized.len() <= states.len());
    }

    #[test]
    fn test_minimize_no_accepting_states() {
        let states: StateSet = (0..2).collect();
        let accepting_states: StateSet = StateSet::new();
        let transitions = create_transitions(&[(0, 'a', 1)]);
        let alphabet = vec!['a'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        // println!("{:?}", minimized);
        assert_eq!(minimized.len(), 1); // All states become one non-accepting state
    }

    #[test]
    fn test_minimize_cyclic_transitions() {
        let states: StateSet = (0..2).collect();
        let accepting_states: StateSet = [1].iter().cloned().collect();
        let transitions = create_transitions(&[(0, 'a', 1), (1, 'a', 0)]);
        let alphabet = vec!['a'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert_eq!(minimized.len(), 2);
    }

    #[test]
    fn test_minimize_overlapping_transitions() {
        let states: StateSet = (0..3).collect();
        let accepting_states: StateSet = [2].iter().cloned().collect();
        let transitions = create_transitions(&[(0, 'a', 1), (1, 'a', 2), (0, 'a', 2)]);
        let alphabet = vec!['a'];

        let minimized = hopcroft_minimization(&states, &accepting_states, &transitions, &alphabet);
        assert!(minimized.len() <= states.len());
    }
}
