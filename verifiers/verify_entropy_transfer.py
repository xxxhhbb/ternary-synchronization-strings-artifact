"""High-precision audit for the local-entropy transfer theorem.

This script checks the transparent 18-uniform, two-choice ternary instance.
It is an auxiliary audit and is not invoked by the paper's proof.
"""

from decimal import Decimal, getcontext


getcontext().prec = 100

q = Decimal(3)
m = 18
K = Decimal(2)
delta = Decimal(1) / 1000
L = 1000
a = Decimal(1) / 80


def binary_entropy(x: Decimal) -> Decimal:
    return -x * x.ln() - (1 - x) * (1 - x).ln()


h = K.ln() / m
b = 2 * K.ln()
phi = 2 * binary_entropy(delta) + delta * (2 * q).ln()
gamma = h - phi - b / L

# Closed forms for sum_{r>L} z^r and sum_{r>L} r z^r.
z = (-a).exp()
zeroth_moment = z ** (L + 1) / (1 - z)
first_moment = (
    z ** (L + 1)
    * (Decimal(L + 1) - Decimal(L) * z)
    / (1 - z) ** 2
)
D = 3 * (zeroth_moment + first_moment / L)

checks = {
    "granularity": Decimal(L) >= Decimal(2 * m + 1),
    "positive_entropy_margin": gamma > 0,
    "charge_below_margin": 0 < a < gamma,
    "small_charge": (-a * L).exp() <= Decimal(1) / 2,
    "lll_closure": a + 2 * D <= gamma,
}

print(f"h                 = {h}")
print(f"Phi_3(1/1000)     = {phi}")
print(f"boundary loss b/L = {b / L}")
print(f"gamma             = {gamma}")
print(f"a                 = {a}")
print(f"D                 = {D}")
print(f"a + 2D            = {a + 2 * D}")
print(f"strict margin      = {gamma - a - 2 * D}")
print(f"exp(-aL)           = {(-a * L).exp()}")
for name, passed in checks.items():
    print(f"{name:24s}: {'PASS' if passed else 'FAIL'}")

if not all(checks.values()):
    raise SystemExit("entropy-transfer audit failed")
