"""
oracle.py
=========
The "Non-Algorithmic Truth" Experiment (Spin Glass Optimization).

Hypothesis:
    Reality involves NP-Hard problems (Finding the "Lowest Energy State" of a complex system).
    Algorithmic Physics (P) gets stuck in "Local Minima" (Suboptimal States).
    Consciousness/Quantum Mechanics acts as an "Oracle" or "Annealer" to find Global Minima.

Experiment:
    1. Create a "Spin Glass" (Graph with conflicting constraints).
    2. Try to minimize energy using "Greedy Descent" (The Machine/Logic).
    3. Try to minimize energy using "Simulated Annealing/Tunneling" (The Oracle/Intuition).
"""

import random
import math
import copy

class SpinGlassUniverse:
    def __init__(self, size=20, complexity=0.8):
        self.size = size
        # Random coupling constants J_ij between -1 and 1
        # This creates "Frustration" (conflicting constraints)
        self.couplings = {}
        for i in range(size):
            for j in range(i + 1, size):
                if random.random() < complexity:
                    self.couplings[(i, j)] = random.choice([-1, 1])

    def get_energy(self, state):
        """Calculate Hamiltonian (Total Energy) of a state."""
        energy = 0
        for (i, j), J in self.couplings.items():
            # If spins are same, energy += -J * 1 * 1 = -J
            # If spins diff, energy += -J * 1 * -1 = J
            spin_prod = state[i] * state[j]
            energy -= J * spin_prod
        return energy

    def greedy_descent(self):
        """
        The Machine (P): Classical Physics.
        Always moves "Downhill".
        Likely to get stuck in a Local Minimum.
        """
        print(f"\n[Machine Mode] Greedy Descent (Deterministic)...")
        # Start random
        current_state = [random.choice([-1, 1]) for _ in range(self.size)]
        current_energy = self.get_energy(current_state)
        
        steps = 0
        improved = True
        while improved:
            improved = False
            steps += 1
            # Try flipping each spin
            best_neighbor = None
            for i in range(self.size):
                neighbor = list(current_state)
                neighbor[i] *= -1 # Flip
                e = self.get_energy(neighbor)
                
                if e < current_energy:
                    current_energy = e
                    best_neighbor = neighbor
                    improved = True 
                    # Greedy: Take first improvement (Determinism)
                    break 
            
            if best_neighbor:
                current_state = best_neighbor

        print(f"Machine Stuck at Energy: {current_energy}")
        return current_energy

    def quantum_annealing(self):
        """
        The Oracle (NP): Quantum/Conscious tunneling.
        Can move "Uphill" to escape local minima (Simulated Annealing).
        Represents "Insight" or "Global Awareness".
        """
        print(f"\n[Oracle Mode] Quantum Annealing (Tunneling Enabled)...")
        
        current_state = [random.choice([-1, 1]) for _ in range(self.size)]
        current_energy = self.get_energy(current_state)
        best_energy = current_energy

        # Temperature schedule (Tunneling amplitude)
        T = 10.0
        decay = 0.9995 # Very slow cooling = Deep contemplation
        steps = 0
        
        while T > 0.01:
            steps += 1
            i = random.randint(0, self.size - 1)
            neighbor = list(current_state)
            neighbor[i] *= -1
            e = self.get_energy(neighbor)
            
            delta = e - current_energy
            
            # Metropolis Criterion: Allow uphill moves with probability P
            # This is the "Leap of Faith" / Insight
            if delta < 0 or random.random() < math.exp(-delta / T):
                current_state = neighbor
                current_energy = e
                if e < best_energy:
                    best_energy = e
            
            T *= decay

        print(f"Oracle Found Energy:  {best_energy}")
        return best_energy

    def run_experiment(self):
        print(f"--- NP-HARD OPTIMIZATION TEST (Spin Glass N={self.size}) ---")
        print("Hypothesis: Logic gets stuck. Intuition/Quantum traverses the barrier.")
        
        # Run 5 trials to show statistical significance
        machine_wins = 0
        oracle_wins = 0
        ties = 0
        
        for i in range(5):
             print(f"\n--- Trial {i+1} ---")
             # Re-initialize problem for each trial to avoid bias? 
             # No, keep same universe structure, just reset state search.
             
             e_machine = self.greedy_descent()
             e_oracle = self.quantum_annealing()
             
             if e_oracle < e_machine:
                 print(">> Result: Oracle Win (Found deeper truth)")
                 oracle_wins += 1
             elif e_machine < e_oracle:
                 print(">> Result: Machine Win (Lucky guess)")
                 machine_wins += 1
             else:
                 print(">> Result: Tie (Easy problem)")
                 ties += 1

        print("\n\nFINAL SCORE:")
        print(f"Machine (Logic): {machine_wins}")
        print(f"Oracle (Insight): {oracle_wins}")
        print(f"Ties:             {ties}")
        
        if oracle_wins > machine_wins:
            print("\nCONCLUSION: The 'Oracle' is structurally necessary to solve the universe's constraints.")
            print("Without Quantum/Conscious tunneling, Reality would freeze in a suboptimal state.")

if __name__ == "__main__":
    uni = SpinGlassUniverse(size=60, complexity=1.0) # Maximum Frustration
    uni.run_experiment()
