% Based on the ILP in "Optimal Correlation Clustering via MaxSAT - Berg & Järvisalo (2014)"

int: n_nodes;

array[1..n_nodes] of set of int: edges;

array[1..n_nodes, 1..n_nodes] of var bool: x;

% Transitivity constraint, if i and j are assigned to the same cluster and j and k are assigned to the same cluster then i and k should also be assigned to the same cluster
constraint forall(i in 1..n_nodes, j in 1..n_nodes, k in 1..n_nodes where i != j /\ j != k)(x[i, j] + x[j, k] <= 1 + x[i, k]);

% For each node, we go over each other node and split into two cases:
%  - If an edge exists in the original graph then we incur cost if it does not exist
%  - If an edge does not exist in the original graph then we incur cost if it exists
solve minimize sum(i in 1..n_nodes)(sum(j in 1..n_nodes)(if j in edges[i] then (1 - x[i, j]) else x[i, j] endif));

% output [concat(["\(i): \([j | j in 1..n_nodes where fix(x[i, j])])\n" | i in 1..n_nodes]) ++ "cost: \(sum(i in 1..n_nodes)(sum(j in 1..n_nodes)(if j in edges[i] then (1 - x[i, j]) else x[i, j] endif)))"];
