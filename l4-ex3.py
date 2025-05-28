import z3


def create_formula(
    nodes: list[str], edges: list[tuple[str, str]], use_at_most_one_node=False
):
    # Create formula using z3.Bool z3.Not z3.And and z3.Or
    # If use_at_most_one_node is True, include that in the formula

    # Make sort and map for nodes from name to z3 const
    NodeSort = z3.DeclareSort("node")
    node_map = {x: z3.Const(x, NodeSort) for x in nodes}

    # Create edge function
    edge = z3.Function("edge", NodeSort, NodeSort, z3.BoolSort())

    # Set of non-edges, for convenience
    non_edges = [(a, b) for a in nodes for b in nodes if (a, b) not in edges]

    # Conjunction of all edges
    true_edges = z3.And(*[edge(node_map[a], node_map[b]) for (a, b) in edges])
    # Conjunction of all non-edges
    false_edges = z3.And(
        *[z3.Not(edge(node_map[a], node_map[b])) for (a, b) in non_edges]
    )

    # Limit the number of surveiled nodes
    surveiled = z3.Function("surveiled", NodeSort, z3.BoolSort())
    limit = z3.AtMost(
        *[surveiled(node_map[x]) for x in nodes], 1 if use_at_most_one_node else 2
    )

    # x, y = z3.Consts("x y", NodeSort)
    # we_surveil_yes = z3.ForAll([x], z3.Implies(
    #     z3.Not(surveiled(x)),
    #     z3.Exists([y], z3.And(edge(x,y), surveiled(y)))
    # ))

    # Homebrew condition: if we do not surveil a node, at least one of its neighbors must be surveiled
    # Make conjunction of all nodes
    homebrew = z3.And(
        *[
            # Disjunction of all neighbors surveilled if we do not surveil this node
            z3.Or(
                *[
                    z3.Implies(z3.Not(surveiled(node_map[a])), surveiled(node_map[b]))
                    for (_a, b) in edges
                    if a == _a
                ]
            )
            for a in nodes
        ]
    )

    # Combine all parts into a single formula
    # first 2 assert that edges are correctly setup
    # Limit asserts how many nodes can be surveilled
    # Homebrew asserts that if a node is not surveilled, at least one of its neighbors is
    formula = z3.And(true_edges, false_edges, limit, homebrew)

    return formula


nodes = ["A", "B", "C", "D", "E", "F"]
edges = [
    ("A", "B"),
    ("A", "D"),
    ("A", "E"),
    ("B", "C"),
    ("B", "E"),
    ("C", "D"),
    ("C", "F"),
    ("D", "E"),
    ("D", "F"),
    ("E", "F"),
]

edges = [e for e in edges] + [(b, a) for (a, b) in edges]

formula = create_formula(nodes, edges)

print("Solution with any number of nodes")
z3.solve(formula)

print("Solution with at most one node")
formula = create_formula(nodes, edges, use_at_most_one_node=True)
z3.solve(formula)
