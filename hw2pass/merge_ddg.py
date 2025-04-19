import sys
import glob
import networkx as nx
from networkx.algorithms.similarity import optimize_graph_edit_distance
from collections import defaultdict, Counter
import matplotlib.pyplot as plt
import os
import itertools
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

def find_most_similar_graph(target_g, graph_list, target_g_idx):
    min_distance = float('inf')
    most_similar_idx = -1
    
    for i, graph in enumerate(graph_list):
        if i == target_g_idx:
            continue
        ged_gen = optimize_graph_edit_distance(
            target_g, graph,
            node_match=node_label_match,
            edge_match=lambda a, b: a.get('label') == b.get('label')
        )
        ged = next(ged_gen)
        if ged < min_distance:
            min_distance, most_similar_idx = ged, i
            
    return most_similar_idx, min_distance


def build_merged_graph(g1: nx.DiGraph, g2: nx.DiGraph):
    merged = nx.DiGraph()

    # Index by label
    g1_label_index = defaultdict(list)
    g2_label_index = defaultdict(list)
    for nid, data in g1.nodes(data=True):
        label = normalize_label(data.get("label", str(nid)))
        g1_label_index[label].append(nid)
    for nid, data in g2.nodes(data=True):
        label = normalize_label(data.get("label", str(nid)))
        g2_label_index[label].append(nid)
    
    # Create node signatures based on connectivity
    def get_signature(graph, node):
        # Get predecessor and successor labels
        pred_labels = Counter([normalize_label(graph.nodes[p].get("label", str(p))) for p in graph.predecessors(node)])
        succ_labels = Counter([normalize_label(graph.nodes[s].get("label", str(s))) for s in graph.successors(node)])
        return pred_labels, succ_labels
    
    # Calculate signatures for all nodes
    g1_sigs = {nid: get_signature(g1, nid) for nid in g1.nodes()}
    g2_sigs = {nid: get_signature(g2, nid) for nid in g2.nodes()}
    
    # Match nodes by label and signature similarity
    node_map = []
    new_id_gen = itertools.count(start=1)
    label_set = set(g1_label_index) | set(g2_label_index)
    
    for label in sorted(label_set):
        g1_ids = g1_label_index.get(label, [])
        g2_ids = g2_label_index.get(label, [])
        
        if g1_ids and g2_ids:
            # Calculate similarity scores for all pairs
            scores = []
            for g1_id in g1_ids:
                g1_pred, g1_succ = g1_sigs[g1_id]
                for g2_id in g2_ids:
                    g2_pred, g2_succ = g2_sigs[g2_id]
                    
                    # Compute similarity based on shared connections
                    pred_sim = sum((g1_pred & g2_pred).values())
                    succ_sim = sum((g1_succ & g2_succ).values())
                    score = pred_sim + succ_sim
                    
                    if score > 0:
                        scores.append((score, g1_id, g2_id))
            
            # Sort by similarity score (highest first)
            scores.sort(reverse=True)
            
            # Greedily match nodes
            matched_g1 = set()
            matched_g2 = set()
            
            for score, g1_id, g2_id in scores:
                if g1_id not in matched_g1 and g2_id not in matched_g2:
                    # Create a merged node for this match
                    node_id = next(new_id_gen)
                    merged.add_node(node_id, label=label, g1_id=g1_id, g2_id=g2_id, origin='both')
                    node_map.append((g1_id, g2_id, node_id))
                    matched_g1.add(g1_id)
                    matched_g2.add(g2_id)
            
            # Add remaining unmatched nodes
            for g1_id in g1_ids:
                if g1_id not in matched_g1:
                    node_id = next(new_id_gen)
                    merged.add_node(node_id, label=label, g1_id=g1_id, g2_id=None, origin='g1_only')
                    node_map.append((g1_id, None, node_id))
            
            for g2_id in g2_ids:
                if g2_id not in matched_g2:
                    node_id = next(new_id_gen)
                    merged.add_node(node_id, label=label, g1_id=None, g2_id=g2_id, origin='g2_only')
                    node_map.append((None, g2_id, node_id))
        else:
            # Add unmatched nodes from either graph
            for g1_id in g1_ids:
                node_id = next(new_id_gen)
                merged.add_node(node_id, label=label, g1_id=g1_id, g2_id=None, origin='g1_only')
                node_map.append((g1_id, None, node_id))
            
            for g2_id in g2_ids:
                node_id = next(new_id_gen)
                merged.add_node(node_id, label=label, g1_id=None, g2_id=g2_id, origin='g2_only')
                node_map.append((None, g2_id, node_id))
    
    # Create reverse mappings
    g1_to_merged = {g1_id: merged_id for (g1_id, _, merged_id) in node_map if g1_id is not None}
    g2_to_merged = {g2_id: merged_id for (_, g2_id, merged_id) in node_map if g2_id is not None}
    
    # Add edges
    for u, v in g1.edges:
        merged.add_edge(g1_to_merged[u], g1_to_merged[v], **{"from": {'g1'}})
    
    for u, v in g2.edges:
        u_merged = g2_to_merged[u]
        v_merged = g2_to_merged[v]
        if merged.has_edge(u_merged, v_merged):
            merged[u_merged][v_merged]['from'].add('g2')
        else:
            merged.add_edge(u_merged, v_merged, **{"from": {'g2'}})
    
    return merged

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
        print(f"g1: {target_graph_index}")
        most_similar_idx, min_distance = find_most_similar_graph(target_graph, graphs, target_graph_index)
        print(f"g2: {most_similar_idx}, distance: {min_distance}")
        merged_graph = build_merged_graph(target_graph, graphs[most_similar_idx])
        output_file = f"{search_pattern}_merged_ddg_{most_similar_idx}.dot"
        nx.drawing.nx_pydot.write_dot(merged_graph, output_file)
        print(f"Merged graph written to {output_file}")
    
    # Visualize all the original graphs
    visualize_all_graphs(all_graphs, search_pattern, output_dir="graph_visualizations", merged_graph=merged_graph)

if __name__ == "__main__":
    main()
