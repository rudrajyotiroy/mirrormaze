import sys
import glob
import networkx as nx
from networkx.algorithms.similarity import optimize_graph_edit_distance
from collections import defaultdict
import matplotlib.pyplot as plt
import os
# ani b - script right now just merges based on the labels - need to tweak it to generate the smallest common supergraph
def normalize_label(label):
    """
    Normalize the label by stripping leading/trailing whitespace.
    Additional normalization (like removing redundant spaces) could be added.
    """
    if label:
        return label.strip()
    return None  # Return None for empty labels

def read_dot_to_graph(dot_file):
    """
    Read a dot file and create a NetworkX graph.
    Returns a NetworkX DiGraph or None if there's an error.
    """
    try:
        g = nx.drawing.nx_pydot.read_dot(dot_file)
        g = nx.DiGraph(g)  # Convert to regular DiGraph
        return g
    except Exception as e:
        print(f"Error reading {dot_file}: {e}")
        return None

def node_label_match(n1_attrs, n2_attrs):
    """Match nodes by label only, ignoring IDs"""
    return n1_attrs.get('label') == n2_attrs.get('label')

def find_most_similar_graph(target_g, graph_list):
    min_distance = float('inf')
    most_similar_idx = -1
    
    for i, graph in enumerate(graph_list):
        ged_gen = optimize_graph_edit_distance(
            target_g, graph,
            node_match=node_label_match,
            edge_match=lambda a, b: a.get('label') == b.get('label')
        )
        ged = next(ged_gen)
        if ged < min_distance:
            min_distance, most_similar_idx = ged, i
            
    return most_similar_idx, min_distance

import networkx as nx
from collections import defaultdict, Counter
import itertools

def build_merged_graph(g1: nx.DiGraph, g2: nx.DiGraph):
    merged = nx.DiGraph()

    # Index by label
    g1_label_index = defaultdict(list)
    g2_label_index = defaultdict(list)
    
    # Extract labels properly, handling potential string formatting
    for nid, data in g1.nodes(data=True):
        label = normalize_label(data.get("label", ""))
        g1_label_index[label].append(nid)
    
    for nid, data in g2.nodes(data=True):
        label = normalize_label(data.get("label", ""))
        g2_label_index[label].append(nid)

    # Match nodes by label
    node_map = []  # tuples of (g1_id or None, g2_id or None, label)
    new_id_gen = itertools.count(start=1)
    label_set = set(g1_label_index) | set(g2_label_index)

    for label in label_set:
        g1_ids = g1_label_index.get(label, [])
        g2_ids = g2_label_index.get(label, [])

        # Match as many as possible
        for g1_id, g2_id in itertools.zip_longest(g1_ids, g2_ids):
            node_id = next(new_id_gen)
            if g1_id is not None and g2_id is not None:
                origin = 'both'
            elif g1_id is not None:
                origin = 'g1_only'
            elif g2_id is not None:
                origin = 'g2_only'
            else:
                origin = 'new'  # shouldn't happen in zip_longest
            merged.add_node(node_id, label=label, g1_id=g1_id, g2_id=g2_id, origin=origin)
            node_map.append((label, g1_id, g2_id, node_id))

    # Reverse maps: g1_id → merged_id, g2_id → merged_id
    g1_to_merged = {g1: nid for (label, g1, _, nid) in node_map if g1 is not None}
    g2_to_merged = {g2: nid for (label, _, g2, nid) in node_map if g2 is not None}

    # Add edges from g1
    for u, v, data in g1.edges(data=True):
        u_m = g1_to_merged[u]
        v_m = g1_to_merged[v]
        if merged.has_edge(u_m, v_m):
            merged[u_m][v_m]['from'].add('g1')
        else:
           merged.add_edge(u_m, v_m, **{"from": {'g1'}})

    # Add edges from g2
    for u, v, data in g2.edges(data=True):
        u_m = g2_to_merged[u]
        v_m = g2_to_merged[v]
        if merged.has_edge(u_m, v_m):
            merged[u_m][v_m]['from'].add('g2')
        else:
            merged.add_edge(u_m, v_m, **{"from": {'g2'}})

    return merged


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

def visualize_graph(graph, title, output_path=None):
    """
    Visualize a graph and save it as an image with clear directed edges.
    
    Args:
        graph: NetworkX graph to visualize
        title: Title for the plot
        output_path: Path to save the image (if None, just displays)
    """
    plt.figure(figsize=(12, 8))
    
    # Extract node labels for display
    node_labels = {node: data.get('label', str(node)) for node, data in graph.nodes(data=True)}
    
    # Try different layouts for better visualization
    # pos = nx.spring_layout(graph, seed=42)  # Original layout
    try:
        # Hierarchical layout often works better for directed graphs
        pos = nx.nx_agraph.graphviz_layout(graph, prog='dot')
    except:
        try:
            # Fall back to another hierarchical layout
            pos = nx.nx_pydot.graphviz_layout(graph, prog='dot')
        except:
            # If graphviz is not available, use spring layout
            pos = nx.spring_layout(graph, seed=42, k=0.5)  # k controls spacing
    
    # Draw nodes with different colors based on origin if available
    node_colors = []
    for node in graph.nodes():
        if 'origin' in graph.nodes[node]:
            if graph.nodes[node]['origin'] == 'both':
                node_colors.append('lightgreen')  # Nodes in both graphs
            elif graph.nodes[node]['origin'] == 'g1_only':
                node_colors.append('lightblue')   # Nodes only in graph 1
            elif graph.nodes[node]['origin'] == 'g2_only':
                node_colors.append('salmon')      # Nodes only in graph 2
            else:
                node_colors.append('lightgray')   # Other nodes
        else:
            node_colors.append('lightgray')       # Default color
    
    # Draw nodes
    nx.draw_networkx_nodes(graph, pos, node_size=700, node_color=node_colors)
    
    # Draw edges with clear arrows
    nx.draw_networkx_edges(
        graph, pos, 
        width=1.5, 
        alpha=0.8, 
        arrows=True,
        arrowsize=20,  # Larger arrows
        arrowstyle='-|>',  # Different arrow style
        connectionstyle='arc3,rad=0.1'  # Curved edges
    )
    
    # Draw labels with better contrast
    nx.draw_networkx_labels(
        graph, pos, 
        labels=node_labels, 
        font_size=8,
        font_weight='bold',
        font_color='black'
    )
    
    # Add a legend
    legend_elements = [
        plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightgreen', markersize=10, label='In Both Graphs'),
        plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightblue', markersize=10, label='Only in Graph 1'),
        plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='salmon', markersize=10, label='Only in Graph 2'),
        plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightgray', markersize=10, label='Other')
    ]
    plt.legend(handles=legend_elements, loc='upper right')
    
    plt.title(title)
    plt.axis('off')  # Turn off axis
    
    # Save or display
    if output_path:
        plt.savefig(output_path, bbox_inches='tight', dpi=300)  # Higher DPI for better quality
        print(f"Graph visualization saved to {output_path}")
    else:
        plt.show()
    
    plt.close()

def visualize_all_graphs(graphs, base_filename, output_dir=None, merged_graph=None):
    """
    Visualize multiple graphs and the merged result.
    
    Args:
        graphs: List of graphs to visualize
        base_filename: Base name for output files
        output_dir: Directory to save images (if None, uses current directory)
        merged_graph: Optional pre-computed merged graph
    """
    if output_dir is None:
        output_dir = '.'
    
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    # Visualize each input graph
    for i, graph in enumerate(graphs):
        output_path = os.path.join(output_dir, f"{base_filename}_graph_{i}.png")
        visualize_graph(graph, f"Graph {i}", output_path)
    
    # If there's a merged graph, visualize it
    if merged_graph is not None:
        output_path = os.path.join(output_dir, f"{base_filename}_merged.png")
        visualize_graph(merged_graph, "Merged Graph", output_path)
    # Otherwise, if there are at least 2 graphs, create and visualize a merged graph
    elif len(graphs) > 1:
        merged = build_merged_graph(graphs[0], graphs[1])
        output_path = os.path.join(output_dir, f"{base_filename}_merged.png")
        visualize_graph(merged, "Merged Graph", output_path)

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 merge_ddg.py <search_pattern>")
        sys.exit(1)
    if len(sys.argv) == 3:
        target_graph_index = int(sys.argv[2])
    else:
        target_graph_index = None

    search_pattern = sys.argv[1]
    # Match only DOT files that contain the search pattern followed by '_ddg_'
    pattern = f"*{search_pattern}_ddg_*.dot"
    dot_files = glob.glob(pattern)

    if not dot_files:
        print(f"No DOT files found for pattern: {pattern}")
        sys.exit(1)

    print("Found DOT files:", dot_files)
    graphs = []
    for dot_file in dot_files:
        g = read_dot_to_graph(dot_file)
        graphs.append(g)
    
    # Keep a copy of all graphs for visualization
    all_graphs = graphs.copy()
    
    # Process graphs for merging
    if target_graph_index is None:
        # target graph is smallest graph
        target_graph = graphs[0]
        graphs.pop(0)
    else:
        target_graph = graphs[target_graph_index]
        graphs.pop(target_graph_index)
        print(f"Target graph: {target_graph_index}")
        most_similar_idx, min_distance = find_most_similar_graph(target_graph, graphs)
        print(f"Most similar graph: {most_similar_idx}, distance: {min_distance}")
        merged_graph = build_merged_graph(target_graph, graphs[most_similar_idx])
        output_file = f"{search_pattern}_merged_ddg_{most_similar_idx}.dot"
        nx.drawing.nx_pydot.write_dot(merged_graph, output_file)
        print(f"Merged graph written to {output_file}")
    
    # Visualize all the original graphs
    visualize_all_graphs(all_graphs, search_pattern, output_dir="graph_visualizations", merged_graph=merged_graph)

if __name__ == "__main__":
    main()
