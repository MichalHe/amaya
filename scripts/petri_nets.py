import numpy as np

# Example in the for the petri net given in Figure 2. of the Liveness of Weighted Circuits and the Diophane 
# Problem of Frobenius paper

m_output = np.array([
    [0, 0, 0, 4], # t1
    [9, 0, 0, 0], # t2
    [0, 5, 0, 0], # t3
    [0, 0, 3, 0], # t4
])

m_input = np.array([
    [5, 0, 0, 0], # t1
    [0, 3, 0, 0], # t2
    [0, 0, 4, 0], # t3
    [0, 0, 0, 9], # t4
])

adj_m = np.transpose(m_input - m_output)  # Transpose so that transitions are columns (to match the paper)
print(f'Adjacency matrix:\n{adj_m}')

# Verify that the matrix is correct
m0 = np.array([9, 0, 0, 0])
m1 = m0 + np.dot(adj_m, np.array([0, 1, 0, 0]))  # Apply the transition t2 once
print(f'Marking {m0} after t2: {m1}')

# Find the P-invariant
# p * adj = 0  --> np.transpose(adj) * np.transpose(p) = np.zeros(0) --> This will not work as the matrix is singular
p = np.array([4, 12, 15, 5])

p_invariant = np.zeros(4, dtype=np.int32)
p_inv_adj = np.copy(adj_m)
for i in range(4):
    column = p_inv_adj[:, i]
    lcm = np.lcm.reduce(np.where((column == 0), np.ones(4, dtype=np.int64), column))
    p_fragment = []
    for j, c in enumerate(column):
        if c != 0:
            multiplier = abs(int(lcm / c))
            p_inv_adj[j] *= multiplier
            p_fragment.append(multiplier)
        else:
            p_fragment.append(0)

    p_fragment = np.abs(np.array(p_fragment))
    p_invariant += p_fragment

# Due to the algorithm above p_invariant contains +1 to every transition, fix it
p_invariant -= np.ones(4, dtype=np.int32)
p_invariant = sorted(p_invariant)

p_invariant_clean = []
for i, p in enumerate(p_invariant):
    is_coprime = True
    for s in p_invariant[:i]:
        # TODO: This should be GCD and only the fractions should be kept. E.g for 3 12 -> 3 4
        if p % s == 0:
            is_coprime = False 
    if is_coprime:
        p_invariant_clean.append(p)

print(f'The p invariant (sorted): {p_invariant}, after removing non-coprime elements: {p_invariant_clean}')
