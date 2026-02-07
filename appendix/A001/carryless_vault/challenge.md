# The “Carryless” Vault Challenge

Break the parametric pairing scheme. Given `(pk, ct)`, recover the full witness `(x, y, p, q)`.

## Theoretical Foundation

Standard Wythoff sequences ($A_k = \lfloor k\phi \rfloor$) are robust. However, **Reflexica** relies on the divergence between the ideal $\phi$ and the certificate $p/q$.

For small indices $k$ and high-precision $p/q$, the map is linear and indistinguishable from $\phi$. To enforce *Hardness*, we must operate at the *Semantic Horizon*—a large numerical offset $\Delta$ where the cumulative error of the rational approximation creates unique, slope-dependent permutations.

```latex

\text{Error} \approx (k + \Delta) \cdot \left| \phi - \frac{p}{q} \right| \ge 1$$

```

At this horizon, even a 1-bit difference in $p$ or $q$ completely scrambles the ciphertext indices (The "Aliasing Event").

## Primitives

### 1. Key Generation (Horizon & Slope)

We generate a rational slope $(p, q)$ and a horizon shift $\Delta$ large enough to sensitize the map.

```python
from decimal import Decimal, getcontext
import random

def keygen(bits):
    """
    Generates a Reflexica Witness.
    - p, q: The rational slope (approx phi).
    - horizon: Large offset to ensure slope sensitivity.
    """
    getcontext().prec = bits * 2
    phi = (Decimal(1).sqrt() + 1) / 2

    # 1. Generate Slope
    q = random.getrandbits(bits)
    p = int(q * phi)
    if q == 0: return keygen(bits)

    # 2. Set Horizon to ensure sensitivity
    # We want (horizon * error) > 1. Error is approx 1/q^2 for convergents, 
    # or 1/q for random. We set horizon ~ q to be safe.
    horizon = random.getrandbits(bits)

    sk = (p, q)
    pk = {'bits': bits, 'horizon': horizon}
    return sk, pk

```

### 2. Forward Map (Horizon-Shifted)

We map logical Zeckendorf indices  to physical positions using the slope and horizon.

```python
def forward_A(k, p, q, horizon):
    # Map (k + horizon) through the slope
    # Lower Wythoff: floor(K * p / q)
    K = k + horizon
    return (K * p) // q

def forward_B(k, p, q, horizon):
    # Upper Wythoff: floor(K * p^2 / q^2)
    K = k + horizon
    return (K * p * p) // (q * q)

```

### 3. Backward Map (The Trapdoor)

Inversion requires exact integer reversibility. The `horizon` is subtracted after inversion.

```python
def invert_A(z, p, q, horizon):
    """
    Solve z = floor(K * p / q) for K, then k = K - horizon.
    """
    # Candidate K = ceil(z * q / p)
    K_candidate = (z * q + p - 1) // p
    
    # Verify exact preimage (Aliasing Check)
    if (K_candidate * p) // q == z:
        k = K_candidate - horizon
        if k >= 0: return k
    return None

def invert_B(z, p, q, horizon):
    """
    Solve z = floor(K * p^2 / q^2) for K.
    """
    num = q * q
    den = p * p
    K_candidate = (z * num + den - 1) // den
    
    if (K_candidate * p * p) // (q * q) == z:
        k = K_candidate - horizon
        if k >= 0: return k
    return None

```

---

## The Protocol

### Encryption (Totality via Re-Keying)

We reject keys that cause collisions (aliasing) for the specific message.

```python
def Enc(x, y, sk, pk):
    p, q = sk
    h = pk['horizon']
    
    Zx = zeckendorf_support(x)
    Zy = zeckendorf_support(y)
    used_indices = set()

    for k in Zx:
        z = forward_A(k, p, q, h)
        if z in used_indices: raise ValueError("Aliasing")
        used_indices.add(z)

    for k in Zy:
        z = forward_B(k, p, q, h)
        if z in used_indices: raise ValueError("Aliasing")
        used_indices.add(z)

    return sum(fib(z) for z in used_indices)

def generate_challenge(key_bits, msg_bits):
    x = random.getrandbits(msg_bits)
    y = random.getrandbits(msg_bits)
    while True:
        try:
            sk, pk = keygen(key_bits)
            ct = Enc(x, y, sk, pk)
            return pk, ct, (x, y, sk[0], sk[1])
        except ValueError:
            continue

```

---

## The Challenge

### Goal

Recover `(x, y, p, q)` given `ct` and `pk` (which contains `horizon`).

### Hardness Argument (Sensitivity)

With `horizon` , the term  is large.
Let  and .
The difference in mapping is:
$$ \Delta z \approx (k + \Delta)(S_1 - S_2) \approx \Delta \cdot \frac{1}{q} $$
If , then .
This means **every single bit** of  and  matters. A 1-bit error in the key shifts the calculated indices by , destroying the Zeckendorf structure of the decrypted text. This eliminates gradient descent attacks.

### Test Tiers

| Tier | Key/Horizon Bits | Msg Bits | Search Space |
| --- | --- | --- | --- |
| **Smoke** | 16 | 32 |  (Brute-forceable) |
| **Core** | 64 | 128 |  (Cluster) |
| **Reflexica** | 256 | 1024 |  (**Hard**) |

---

## Reference Adversary

```python
def solve(ct, pk):
    """
    Constraint Solving Attack.
    The presence of 'horizon' makes this a Diophantine approximation 
    problem with large coefficients.
    """
    target_bits = pk['bits']
    h = pk['horizon']
    
    # Search for slope p/q
    for q in enumerate_large_integers(target_bits):
        p = round(q * PHI)
        
        # Inversion Check
        try:
            indices = zeckendorf_support(ct)
            x_k, y_k = [], []
            
            for z in indices:
                ka = invert_A(z, p, q, h)
                kb = invert_B(z, p, q, h)
                
                # Strict separation required
                if ka is not None and kb is None: x_k.append(ka)
                elif kb is not None and ka is None: y_k.append(kb)
                else: raise InvalidKeyError()
            
            x, y = reconstruct(x_k), reconstruct(y_k)
            # Verify exact re-encoding
            if Enc(x, y, (p,q), pk) == ct:
                return x, y, p, q
        except:
            continue

```
