import sys
import glob
import networkx as nx
# ani b - script right now just merges based on the labels - need to tweak it to generate the smallest common supergraph
def normalize_label(label):
    """
    Normalize the label by stripping leading/trailing whitespace.
    Additional normalization (like removing redundant spaces) could be added.
    """
    if label:
        return label.strip()
    return None  # Return None for empty labels

def merge_ddg_dot_files(dot_files):
    supergraph = nx.DiGraph()

    # A mapping from normalized label -> node identifier in supergraph
    node_map = {}

    for dot_file in dot_files:
        try:
            # Read the DOT file via the pydot interface
            g = nx.drawing.nx_pydot.read_dot(dot_file)
        except Exception as e:
            print(f"Error reading {dot_file}: {e}")
            continue

        # Process nodes: each node is keyed by its identifier in the DOT file,
        # but we rely on the "label" attribute (normalized) as the unique key.
        for node, attr in g.nodes(data=True):
            raw_label = attr.get('label', '')
            norm_label = normalize_label(raw_label)
            if norm_label is None or norm_label == "":
                # Skip nodes with empty labels.
                continue
            if norm_label not in node_map:
                # Add the node using the normalized label as key.
                supergraph.add_node(norm_label, label=norm_label)
                node_map[norm_label] = norm_label

        # Process edges: use normalized labels for both ends.
        for u, v, attr in g.edges(data=True):
            raw_u = g.nodes[u].get('label', '')
            raw_v = g.nodes[v].get('label', '')
            norm_u = normalize_label(raw_u)
            norm_v = normalize_label(raw_v)
            # Only process this edge if both endpoints have non-empty normalized labels.
            if norm_u is None or norm_v is None or norm_u == "" or norm_v == "":
                continue
            # Ensure both nodes have already been added to the supergraph.
            if norm_u in node_map and norm_v in node_map:
                # Add the edge only if it doesn't already exist.
                if not supergraph.has_edge(norm_u, norm_v):
                    supergraph.add_edge(norm_u, norm_v, **attr)

    return supergraph

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 merge_ddg.py <search_pattern>")
        sys.exit(1)

    search_pattern = sys.argv[1]
    # Match only DOT files that contain the search pattern followed by '_ddg_'
    pattern = f"*{search_pattern}_ddg_*.dot"
    dot_files = glob.glob(pattern)

    if not dot_files:
        print(f"No DOT files found for pattern: {pattern}")
        sys.exit(1)

    print("Found DOT files:", dot_files)

    supergraph = merge_ddg_dot_files(dot_files)

    # Write the merged supergraph to a DOT file with a name based on the search pattern.
    output_file = f"{search_pattern}_supergraph.dot"
    nx.drawing.nx_pydot.write_dot(supergraph, output_file)
    print(f"Supergraph written to {output_file}")

if __name__ == "__main__":
    main()
