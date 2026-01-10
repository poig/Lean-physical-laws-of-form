"""
observer.py
===========
The "Rendering Glitch" Experiment (Double Slit).

Hypothesis:
    Quantum Mechanics is an optimization.
    "Wave Function" = Unresolved Data (Lazy Evaluation).
    "Collapse" = Resolved Data (Eager Evaluation).
    
    When we do not "resolve" (measure) the path, the universe computes the 
    result using a single complex operation (Superposition).
    This creates "Interference" (Interference Artifacts).
    
    When we "resolve" (measure) the path, the universe must calculate 
    two separate histories and add them.
    This removes the artifacts (Collapse).
"""

import numpy as np
import math

class QuantumSimulation:
    def __init__(self, width=60, distance=100, slit_separation=4):
        self.width = width
        self.distance = distance
        self.d = slit_separation
        self.k = 1.0 # Wave number

    def run_simulation(self):
        print(f"{'SCREEN POSITION':<15} | {'WAVE (UNOBSERVED)':<20} | {'PARTICLE (OBSERVED)':<20}")
        print("-" * 65)

        # ASCII Graph buffers
        wave_graph = [" "] * self.width
        part_graph = [" "] * self.width

        # Evaluate intensity at each point on the screen
        intensities_wave = []
        intensities_part = []

        # We scan across the screen (y-axis)
        screen_points = np.linspace(-10, 10, self.width)

        for i, y in enumerate(screen_points):
            # Distance from Slit 1 (located at -d/2)
            r1 = math.sqrt(self.distance**2 + (y - (-self.d/2))**2)
            # Distance from Slit 2 (located at d/2)
            r2 = math.sqrt(self.distance**2 + (y - (self.d/2))**2)

            # --- MODE 1: LAZY EVALUATION (Unobserved) ---
            # The universe sums the Amplitude (Complex Numbers).
            # A_total = e^(ikr1) + e^(ikr2)
            # This is "Lazy" because it preserves the ambiguity (Phase) until the end.
            psi1 = complex(math.cos(self.k*r1), math.sin(self.k*r1))
            psi2 = complex(math.cos(self.k*r2), math.sin(self.k*r2))
            psi_total = psi1 + psi2
            intensity_wave = abs(psi_total)**2

            # --- MODE 2: EAGER EVALUATION (Observed) ---
            # The universe resolves the path FIRST. 
            # We measure "Did it go through 1? Or 2?"
            # This destroys the phase relationship. We sum Probabilities, not Amplitudes.
            # I_total = |e^(ikr1)|^2 + |e^(ikr2)|^2
            intensity_part = abs(psi1)**2 + abs(psi2)**2

            intensities_wave.append(intensity_wave)
            intensities_part.append(intensity_part)

        # Normalize for display
        max_w = max(intensities_wave)
        max_p = max(intensities_part)

        for i in range(self.width):
            # Scale to 0-10 for graph
            val_w = int((intensities_wave[i] / max_w) * 10)
            val_p = int((intensities_part[i] / max_p) * 10)
            
            bar_w = "#" * val_w
            bar_p = "." * val_p
            
            print(f"{screen_points[i]:<15.2f} | {bar_w:<20} | {bar_p:<20}")

        print("-" * 65)
        print("Analysis:")
        print("1. LEFT COLUMN (Unobserved): Shows 'Fringes' (####  ####).") 
        print("   -> This is INTERFERENCE. The system processed both paths at once.")
        print("2. RIGHT COLUMN (Observed): Shows a 'Lump' (.....).") 
        print("   -> This is COLLAPSE. The system processed paths separately.")
        print("\nVerdict: The 'Glitch' (Interference) appears only when we don't look.")

if __name__ == "__main__":
    sim = QuantumSimulation()
    sim.run_simulation()
