#!/usr/bin/env python3
"""
Generate dependency graph visualizations for the Lean Ethereum PQ Crypto bundle.

Creates:
- DOT file for Graphviz
- HTML file with interactive 3D visualization using vis.js
"""

import json
from pathlib import Path

MODULES = [
    ("IncomparableEncoding", "Crypto.PostQuantum", "#ef4444"),  # Red - crypto
    ("Poseidon2", "Crypto.PostQuantum", "#ef4444"),
    ("XMSS", "Crypto.PostQuantum", "#ef4444"),
    ("Multilinear", "Crypto.PIOP", "#8b5cf6"),  # Purple - PIOP
    ("Sumcheck", "Crypto.PIOP", "#8b5cf6"),
    ("FiatShamir", "Crypto.PIOP", "#8b5cf6"),
    ("MessageModelSeq", "Blockchain.Bridge", "#22c55e"),  # Green - blockchain
    ("PostQuantumHTLC", "Blockchain.PaymentChannels", "#22c55e"),
]

EDGES = [
    ("XMSS", "IncomparableEncoding"),
    ("Sumcheck", "Multilinear"),
    ("FiatShamir", "Sumcheck"),
    ("PostQuantumHTLC", "MessageModelSeq"),
    ("PostQuantumHTLC", "XMSS"),
]

def generate_dot():
    """Generate Graphviz DOT file."""
    lines = [
        'digraph LeanEthereumPQ {',
        '  rankdir=TB;',
        '  node [shape=box, style="rounded,filled", fontname="Arial"];',
        '  edge [color="#64748b"];',
        '',
        '  // Subgraphs for clustering',
        '  subgraph cluster_pq {',
        '    label="Post-Quantum Signatures";',
        '    style=dashed;',
        '    color="#ef4444";',
    ]

    for name, ns, color in MODULES:
        if "PostQuantum" in ns:
            lines.append(f'    {name} [fillcolor="{color}20", color="{color}"];')

    lines.extend([
        '  }',
        '',
        '  subgraph cluster_piop {',
        '    label="Polynomial IOPs";',
        '    style=dashed;',
        '    color="#8b5cf6";',
    ])

    for name, ns, color in MODULES:
        if "PIOP" in ns:
            lines.append(f'    {name} [fillcolor="{color}20", color="{color}"];')

    lines.extend([
        '  }',
        '',
        '  subgraph cluster_blockchain {',
        '    label="Blockchain / Payment Channels";',
        '    style=dashed;',
        '    color="#22c55e";',
    ])

    for name, ns, color in MODULES:
        if "Blockchain" in ns:
            lines.append(f'    {name} [fillcolor="{color}20", color="{color}"];')

    lines.extend([
        '  }',
        '',
        '  // Edges',
    ])

    for src, dst in EDGES:
        lines.append(f'  {src} -> {dst};')

    lines.append('}')
    return '\n'.join(lines)


def generate_3d_html():
    """Generate interactive 3D visualization HTML."""
    nodes = []
    for i, (name, ns, color) in enumerate(MODULES):
        # Position nodes in 3D space by category
        if "PostQuantum" in ns:
            x, z = -100, 0
        elif "PIOP" in ns:
            x, z = 100, 0
        else:
            x, z = 0, 100
        y = (i % 3) * 80 - 80

        nodes.append({
            "id": name,
            "label": name,
            "x": x + (i % 2) * 40,
            "y": y,
            "z": z,
            "color": color,
            "namespace": ns
        })

    edges = [{"from": src, "to": dst} for src, dst in EDGES]

    html = f'''<!DOCTYPE html>
<html>
<head>
    <title>Lean Ethereum PQ Crypto - 3D Module Graph</title>
    <script src="https://unpkg.com/vis-network/standalone/umd/vis-network.min.js"></script>
    <style>
        body {{ margin: 0; padding: 20px; font-family: Arial, sans-serif; background: #0f172a; color: white; }}
        h1 {{ text-align: center; }}
        #graph {{ width: 100%; height: 600px; border: 1px solid #334155; border-radius: 8px; }}
        .legend {{ display: flex; justify-content: center; gap: 30px; margin: 20px 0; }}
        .legend-item {{ display: flex; align-items: center; gap: 8px; }}
        .legend-color {{ width: 20px; height: 20px; border-radius: 4px; }}
    </style>
</head>
<body>
    <h1>Lean Ethereum Post-Quantum Crypto Module Graph</h1>
    <div class="legend">
        <div class="legend-item"><div class="legend-color" style="background:#ef4444"></div>Post-Quantum Signatures</div>
        <div class="legend-item"><div class="legend-color" style="background:#8b5cf6"></div>Polynomial IOPs</div>
        <div class="legend-item"><div class="legend-color" style="background:#22c55e"></div>Blockchain</div>
    </div>
    <div id="graph"></div>
    <script>
        var nodes = new vis.DataSet({json.dumps(nodes)});
        var edges = new vis.DataSet({json.dumps(edges)});
        var container = document.getElementById('graph');
        var data = {{ nodes: nodes, edges: edges }};
        var options = {{
            nodes: {{
                shape: 'box',
                font: {{ color: 'white', size: 14 }},
                borderWidth: 2,
                shadow: true
            }},
            edges: {{
                arrows: 'to',
                color: '#64748b',
                width: 2
            }},
            physics: {{
                enabled: true,
                barnesHut: {{ gravitationalConstant: -2000 }}
            }},
            interaction: {{ hover: true }}
        }};
        var network = new vis.Network(container, data, options);
    </script>
</body>
</html>'''
    return html


if __name__ == "__main__":
    script_dir = Path(__file__).parent
    output_dir = script_dir.parent / "artifacts" / "visuals"
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate DOT
    dot_content = generate_dot()
    (output_dir / "module_graph.dot").write_text(dot_content)
    print(f"Generated: {output_dir / 'module_graph.dot'}")

    # Generate 3D HTML
    html_content = generate_3d_html()
    (output_dir / "module_graph_3d.html").write_text(html_content)
    print(f"Generated: {output_dir / 'module_graph_3d.html'}")

    print("\nTo render DOT as PNG: dot -Tpng module_graph.dot -o module_graph.png")
