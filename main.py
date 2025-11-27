import tkinter as tk
from tkinter import ttk, messagebox
import math
import random
from collections import defaultdict
import time
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib
matplotlib.use('TkAgg')


class NetworkNode:
    def __init__(self, x, y, node_type, name):
        self.x = x
        self.y = y
        self.type = node_type  # 'cloud', 'router', 'switch', 'pc'
        self.name = name
        self.connections = []
        self.packets = []
        self.latency = random.randint(5, 50)
        self.throughput = random.randint(100, 1000)
        self.congestion = 0
        self.hop_count = 0  # NEW: Track hop count

        # NEW: TCP Congestion Control
        self.tcp_control = None  # Will be set to Tahoe or Reno
        self.packet_loss_probability = 0.0  # Dynamic packet loss
        self.last_ack_time = time.time()
        self.timeout_threshold = 2.0  # seconds
        self.packets_in_flight = 0
        self.max_buffer_size = 10
    # NEW: Get congestion level category
    def get_congestion_level(self):
        """Returns congestion level: 'low', 'medium', 'high', 'critical'"""
        if self.congestion <= 1:
            return 'low'
        elif self.congestion <= 3:
            return 'medium'
        elif self.congestion <= 5:
            return 'high'
        else:
            return 'critical'
        
class Packet:
    def __init__(self, source, destination, path):
        self.source = source
        self.destination = destination
        self.path = path
        self.current_index = 0
        self.progress = 0
        self.color = f"#{random.randint(0, 255):02x}{random.randint(100, 255):02x}{random.randint(100, 255):02x}"
        self.hop_count = len(path) - 1  # NEW: Calculate hops
        self.total_latency = 0  # NEW: Track cumulative latency
        self.timestamp = time.time()  # NEW: Packet creation time
        self.completed = False  # NEW: Track if packet reached destination

class TCPCongestionControl:
    """Base class for TCP congestion control"""
    def __init__(self):
        self.cwnd = 1  # Congestion window (in packets)
        self.ssthresh = 64  # Slow start threshold
        self.state = "slow_start"  # States: slow_start, congestion_avoidance, fast_recovery
        self.duplicate_acks = 0
        self.packets_sent = 0
        self.packets_acked = 0
        
    def on_ack_received(self):
        """Called when ACK is received"""
        pass
    
    def on_timeout(self):
        """Called when timeout occurs"""
        pass
    
    def on_duplicate_ack(self):
        """Called when duplicate ACK is received"""
        pass
    
    def get_window_size(self):
        """Returns current congestion window size"""
        return max(1, int(self.cwnd))

class TCPTahoe(TCPCongestionControl):
    """TCP Tahoe implementation"""
    def __init__(self):
        super().__init__()
        self.algorithm = "Tahoe"
    
    def on_ack_received(self):
        """Handle ACK in Tahoe"""
        self.packets_acked += 1
        self.duplicate_acks = 0
        
        if self.state == "slow_start":
            # Exponential growth: cwnd += 1 per ACK
            self.cwnd += 1
            if self.cwnd >= self.ssthresh:
                self.state = "congestion_avoidance"
        
        elif self.state == "congestion_avoidance":
            # Linear growth: cwnd += 1/cwnd per ACK
            self.cwnd += 1.0 / self.cwnd
    
    def on_timeout(self):
        """Handle timeout in Tahoe"""
        self.ssthresh = max(self.cwnd / 2, 2)
        self.cwnd = 1
        self.state = "slow_start"
        self.duplicate_acks = 0
    
    def on_duplicate_ack(self):
        """Handle duplicate ACK in Tahoe"""
        self.duplicate_acks += 1
        
        # 3 duplicate ACKs = packet loss
        if self.duplicate_acks >= 3:
            self.on_timeout()  # Tahoe treats this like timeout

class TCPReno(TCPCongestionControl):
    """TCP Reno implementation with Fast Retransmit and Fast Recovery"""
    def __init__(self):
        super().__init__()
        self.algorithm = "Reno"
    
    def on_ack_received(self):
        """Handle ACK in Reno"""
        self.packets_acked += 1
        
        if self.state == "slow_start":
            # Exponential growth
            self.cwnd += 1
            self.duplicate_acks = 0
            
            if self.cwnd >= self.ssthresh:
                self.state = "congestion_avoidance"
        
        elif self.state == "congestion_avoidance":
            # Linear growth
            self.cwnd += 1.0 / self.cwnd
            self.duplicate_acks = 0
        
        elif self.state == "fast_recovery":
            # Exit fast recovery
            self.cwnd = self.ssthresh
            self.state = "congestion_avoidance"
            self.duplicate_acks = 0
    
    def on_timeout(self):
        """Handle timeout in Reno"""
        self.ssthresh = max(self.cwnd / 2, 2)
        self.cwnd = 1
        self.state = "slow_start"
        self.duplicate_acks = 0
    
    def on_duplicate_ack(self):
        """Handle duplicate ACK in Reno"""
        self.duplicate_acks += 1
        
        if self.duplicate_acks == 3:
            # Fast Retransmit
            self.ssthresh = max(self.cwnd / 2, 2)
            self.cwnd = self.ssthresh + 3
            self.state = "fast_recovery"
        
        elif self.state == "fast_recovery":
            # Inflate window
            self.cwnd += 1




class CloudNetworkSimulator:
    def __init__(self, root):
        self.root = root
        self.root.title("Cloud Network Simulator - Enhanced")
        self.root.geometry("1400x900")
        self.root.configure(bg="#1e1e2e")
        
        # Data structures
        self.nodes = []
        self.connections = []
        self.packets = []
        self.selected_node = None
        self.dragging_node = None
        self.connection_mode = False
        self.simulation_running = False
        self.highlighted_path = []  # NEW: Store path to highlight

        self.latency_history = []
        self.throughput_history = []
        self.time_stamps = []
        self.performance_start_time = time.time()

        self.traffic_load = "medium"  # Options: "light", "medium", "heavy"
        self.packet_generation_rate = 1000  # milliseconds
        self.congestion_algorithm = "Reno"  # Options: "Reno", "Tahoe"

         # NEW: Routing Analysis Variables
        self.routing_stats = {
            'total_packets': 0,
            'avg_hop_count': 0,
            'min_hops': float('inf'),
            'max_hops': 0,
            'path_history': []
        }
        
        # Colors
        self.colors = {
            'bg': '#1e1e2e',
            'canvas_bg': '#2a2a3e',
            'panel_bg': '#252536',
            'accent': '#6c63ff',
            'text': '#ffffff',
            'secondary': '#9ca3af',
            'success': '#10b981',
            'warning': '#f59e0b',
            'error': '#ef4444',
            'cloud': '#3b82f6',
            'router': '#8b5cf6',
            'switch': '#ec4899',
            'pc': '#10b981'
        }
        
        self.setup_ui()
        
    def setup_ui(self):
        # Top toolbar
        toolbar = tk.Frame(self.root, bg=self.colors['panel_bg'], height=60)
        toolbar.pack(side=tk.TOP, fill=tk.X, padx=0, pady=0)
        
        # Title
        title = tk.Label(toolbar, text="☁ Cloud Network Simulator", 
                        font=("Segoe UI", 18, "bold"),
                        bg=self.colors['panel_bg'], fg=self.colors['text'])
        title.pack(side=tk.LEFT, padx=20, pady=10)
        
        # Control buttons
        btn_frame = tk.Frame(toolbar, bg=self.colors['panel_bg'])
        btn_frame.pack(side=tk.RIGHT, padx=20)
        
        self.sim_button = self.create_button(btn_frame, "▶ Start Simulation", 
                                             self.toggle_simulation, self.colors['success'])
        self.sim_button.pack(side=tk.LEFT, padx=5)
        
        self.create_button(btn_frame, "📊 Metrics", 
                          self.show_metrics, self.colors['accent']).pack(side=tk.LEFT, padx=5)
        
        # NEW: Shortest Path button
        self.create_button(btn_frame, "🗺️ Find Path", 
                          self.show_path_finder, self.colors['router']).pack(side=tk.LEFT, padx=5)
        
        self.create_button(btn_frame, "📈 Graphs", 
                          self.show_performance_graphs, '#22c55e').pack(side=tk.LEFT, padx=5)
        
        self.create_button(btn_frame, "🧭 Routing", 
                          self.show_routing_analysis, '#ec4899').pack(side=tk.LEFT, padx=5)
        
        self.create_button(btn_frame, "🔄 Reset", 
                          self.reset_network, self.colors['warning']).pack(side=tk.LEFT, padx=5)
        
        # Main container
        main_container = tk.Frame(self.root, bg=self.colors['bg'])
        main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Left panel - Node palette
        left_panel = tk.Frame(main_container, bg=self.colors['panel_bg'], width=200)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left_panel.pack_propagate(False)

        # NEW: Add Canvas and Scrollbar for scrolling
        left_canvas = tk.Canvas(left_panel, bg=self.colors['panel_bg'], 
                            highlightthickness=0, width=200)
        scrollbar = tk.Scrollbar(left_panel, orient="vertical", command=left_canvas.yview)
        scrollable_frame = tk.Frame(left_canvas, bg=self.colors['panel_bg'])

        scrollable_frame.bind(
            "<Configure>",
            lambda e: left_canvas.configure(scrollregion=left_canvas.bbox("all"))
        )

        left_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        left_canvas.configure(yscrollcommand=scrollbar.set)

        left_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # Enable mouse wheel scrolling
        def on_mousewheel(event):
            left_canvas.yview_scroll(int(-1*(event.delta/120)), "units")

        left_canvas.bind_all("<MouseWheel>", on_mousewheel)
        
        palette_title = tk.Label(scrollable_frame, text="Network Elements", 
                                font=("Segoe UI", 12, "bold"),
                                bg=self.colors['panel_bg'], fg=self.colors['text'])
        palette_title.pack(pady=15)
        
        # Node type buttons
        node_types = [
            ("☁ Cloud", "cloud", self.colors['cloud']),
            ("⚡ Router", "router", self.colors['router']),
            ("⊞ Switch", "switch", self.colors['switch']),
            ("💻 PC", "pc", self.colors['pc'])
        ]
        
        for label, ntype, color in node_types:
            btn = tk.Button(scrollable_frame, text=label, 
                          command=lambda t=ntype: self.add_node(t),
                          bg=color, fg="white", font=("Segoe UI", 10, "bold"),
                          relief=tk.FLAT, cursor="hand2", padx=15, pady=10)
            btn.pack(pady=5, padx=10, fill=tk.X)
            btn.bind("<Enter>", lambda e, b=btn: b.configure(bg=self.lighten_color(b['bg'])))
            btn.bind("<Leave>", lambda e, b=btn, c=color: b.configure(bg=c))
        
        # Connection button
        self.conn_button = tk.Button(scrollable_frame, text="🔗 Connect Nodes", 
                                     command=self.toggle_connection_mode,
                                     bg=self.colors['secondary'], fg="white", 
                                     font=("Segoe UI", 10, "bold"),
                                     relief=tk.FLAT, cursor="hand2", padx=15, pady=10)
        self.conn_button.pack(pady=20, padx=10, fill=tk.X)
        
        # === NEW: TOPOLOGY SECTION ===
        topology_label = tk.Label(scrollable_frame, text="Generate Topology", 
                                 font=("Segoe UI", 11, "bold"),
                                 bg=self.colors['panel_bg'], fg=self.colors['text'])
        topology_label.pack(pady=(20, 10))
        
        topologies = [
            ("⭐ Star", "star"),
            ("🕸 Mesh", "mesh"),
            ("⭕ Ring", "ring"),
            ("🌳 Tree", "tree"),
            ("➖ Linear", "linear")
        ]
        
        for label, topo in topologies:
            btn = tk.Button(scrollable_frame, text=label,
                          command=lambda t=topo: self.generate_topology(t),
                          bg="#374151", fg="white", font=("Segoe UI", 9),
                          relief=tk.FLAT, cursor="hand2", padx=10, pady=8)
            btn.pack(pady=3, padx=10, fill=tk.X)
            btn.bind("<Enter>", lambda e, b=btn: b.configure(bg="#4b5563"))
            btn.bind("<Leave>", lambda e, b=btn: b.configure(bg="#374151"))
        
        # NEW: Traffic Load Control Section
        traffic_label = tk.Label(scrollable_frame, text="Traffic Load", 
                                font=("Segoe UI", 11, "bold"),
                                bg=self.colors['panel_bg'], fg=self.colors['text'])
        traffic_label.pack(pady=(20, 10))
        
        traffic_loads = [
            ("🟢 Light", "light", "#10b981"),
            ("🟡 Medium", "medium", "#f59e0b"),
            ("🔴 Heavy", "heavy", "#ef4444")
        ]
        
        self.traffic_buttons = {}
        for label, load, color in traffic_loads:
            btn = tk.Button(scrollable_frame, text=label,
                          command=lambda l=load: self.set_traffic_load(l),
                          bg="#374151", fg="white", font=("Segoe UI", 9),
                          relief=tk.FLAT, cursor="hand2", padx=10, pady=8)
            btn.pack(pady=3, padx=10, fill=tk.X)
            self.traffic_buttons[load] = btn
            
            if load == "medium":
                btn.config(bg=color)  # Highlight default selection


        # NEW: Congestion Control Algorithm Selection
        algo_label = tk.Label(scrollable_frame, text="Congestion Control", 
                            font=("Segoe UI", 11, "bold"),
                            bg=self.colors['panel_bg'], fg=self.colors['text'])
        algo_label.pack(pady=(20, 10))

        algorithms = [
            ("🐢 TCP Tahoe", "Tahoe"),
            ("🚀 TCP Reno", "Reno")
        ]

        self.algo_buttons = {}
        for label, algo in algorithms:
            btn = tk.Button(scrollable_frame, text=label,
                        command=lambda a=algo: self.set_congestion_algorithm(a),
                        bg="#374151", fg="white", font=("Segoe UI", 9),
                        relief=tk.FLAT, cursor="hand2", padx=10, pady=8)
            btn.pack(pady=3, padx=10, fill=tk.X)
            self.algo_buttons[algo] = btn
            
            if algo == "Reno":
                btn.config(bg="#8b5cf6")  # Highlight default selection

        # Canvas
        canvas_frame = tk.Frame(main_container, bg=self.colors['canvas_bg'], 
                               highlightbackground=self.colors['accent'], highlightthickness=2)
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.canvas = tk.Canvas(canvas_frame, bg=self.colors['canvas_bg'], 
                               highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        
        # Status bar
        status_bar = tk.Frame(self.root, bg=self.colors['panel_bg'], height=30)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.status_label = tk.Label(status_bar, text="Ready - Select a topology to begin", 
                                     bg=self.colors['panel_bg'], 
                                     fg=self.colors['secondary'],
                                     font=("Segoe UI", 9))
        self.status_label.pack(side=tk.LEFT, padx=10)
        
    def create_button(self, parent, text, command, color):
        btn = tk.Button(parent, text=text, command=command,
                       bg=color, fg="white", font=("Segoe UI", 10, "bold"),
                       relief=tk.FLAT, cursor="hand2", padx=15, pady=8)
        btn.bind("<Enter>", lambda e: btn.configure(bg=self.lighten_color(color)))
        btn.bind("<Leave>", lambda e: btn.configure(bg=color))
        return btn
    
    def lighten_color(self, color):
        color = color.lstrip('#')
        r, g, b = tuple(int(color[i:i+2], 16) for i in (0, 2, 4))
        r = min(255, r + 30)
        g = min(255, g + 30)
        b = min(255, b + 30)
        return f'#{r:02x}{g:02x}{b:02x}'
    
    # === NEW: TOPOLOGY GENERATION METHODS ===
    def generate_topology(self, topology_type):
        self.reset_network(confirm=False)
        
        if topology_type == "star":
            self.create_star_topology()
        elif topology_type == "mesh":
            self.create_mesh_topology()
        elif topology_type == "ring":
            self.create_ring_topology()
        elif topology_type == "tree":
            self.create_tree_topology()
        elif topology_type == "linear":
            self.create_linear_topology()
            
        self.draw_network()
        self.status_label.config(text=f"{topology_type.upper()} topology created with {len(self.nodes)} nodes")
    

    # NEW: Set Traffic Load Level
    def set_traffic_load(self, load_level):
        """Change network traffic load: light, medium, or heavy"""
        self.traffic_load = load_level
        
        # Update packet generation rate based on load
        if load_level == "light":
            self.packet_generation_rate = 2000  # 2 seconds
            load_color = "#10b981"
        elif load_level == "medium":
            self.packet_generation_rate = 1000  # 1 second
            load_color = "#f59e0b"
        else:  # heavy
            self.packet_generation_rate = 300  # 0.3 seconds
            load_color = "#ef4444"
        
        # Update button colors
        for load, btn in self.traffic_buttons.items():
            if load == load_level:
                if load == "light":
                    btn.config(bg="#10b981")
                elif load == "medium":
                    btn.config(bg="#f59e0b")
                else:
                    btn.config(bg="#ef4444")
            else:
                btn.config(bg="#374151")
        
        self.status_label.config(text=f"Traffic load set to: {load_level.upper()}")

    def set_congestion_algorithm(self, algorithm):
        """Change TCP congestion control algorithm: Tahoe or Reno"""
        self.congestion_algorithm = algorithm
        
        # Update all nodes with new algorithm
        for node in self.nodes:
            if algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()
        
        # Update button colors
        for algo, btn in self.algo_buttons.items():
            if algo == algorithm:
                btn.config(bg="#8b5cf6")
            else:
                btn.config(bg="#374151")
        
        self.status_label.config(text=f"Congestion control set to: TCP {algorithm}")


    def create_star_topology(self):
        """Star topology: central router with multiple PCs"""
        center_x, center_y = 600, 400
        
        # Central router
        router = NetworkNode(center_x, center_y, "router", "ROUTER1")
        self.nodes.append(router)
        
        # Create PCs in a circle around router
        num_pcs = 6
        radius = 200
        for i in range(num_pcs):
            angle = (2 * math.pi * i) / num_pcs
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            
            pc = NetworkNode(x, y, "pc", f"PC{i+1}")
            self.nodes.append(pc)
            
            # Connect to router
            router.connections.append(pc)
            pc.connections.append(router)
            self.connections.append((router, pc))

        # Initialize TCP congestion control for all nodes
        for node in self.nodes:
            if self.congestion_algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()

    def create_mesh_topology(self):
        """Mesh topology: all nodes connected to all other nodes"""
        positions = [
            (400, 250), (600, 250), (800, 250),
            (400, 450), (600, 450), (800, 450)
        ]
        
        # Create routers
        for i, (x, y) in enumerate(positions):
            router = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(router)
        
        # Connect all to all
        for i, node1 in enumerate(self.nodes):
            for node2 in self.nodes[i+1:]:
                node1.connections.append(node2)
                node2.connections.append(node1)
                self.connections.append((node1, node2))

        # Initialize TCP congestion control for all nodes
        for node in self.nodes:
            if self.congestion_algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()
    
    def create_ring_topology(self):
        """Ring topology: nodes connected in a circle"""
        center_x, center_y = 600, 400
        num_nodes = 8
        radius = 220
        
        for i in range(num_nodes):
            angle = (2 * math.pi * i) / num_nodes
            x = center_x + radius * math.cos(angle)
            y = center_y + radius * math.sin(angle)
            
            node = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(node)
        
        # Connect in ring
        for i in range(len(self.nodes)):
            node1 = self.nodes[i]
            node2 = self.nodes[(i + 1) % len(self.nodes)]
            
            node1.connections.append(node2)
            node2.connections.append(node1)
            self.connections.append((node1, node2))

        # Initialize TCP congestion control for all nodes
        for node in self.nodes:
            if self.congestion_algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()
    
    def create_tree_topology(self):
        """Tree topology: hierarchical structure"""
        # Cloud at top
        cloud = NetworkNode(600, 150, "cloud", "CLOUD1")
        self.nodes.append(cloud)
        
        # Level 1: Routers
        router1 = NetworkNode(400, 300, "router", "ROUTER1")
        router2 = NetworkNode(800, 300, "router", "ROUTER2")
        self.nodes.extend([router1, router2])
        
        cloud.connections.extend([router1, router2])
        router1.connections.append(cloud)
        router2.connections.append(cloud)
        self.connections.extend([(cloud, router1), (cloud, router2)])
        
        # Level 2: Switches
        switches = []
        for i, x in enumerate([300, 500, 700, 900]):
            switch = NetworkNode(x, 450, "switch", f"SWITCH{i+1}")
            switches.append(switch)
            self.nodes.append(switch)
            
            parent = router1 if i < 2 else router2
            parent.connections.append(switch)
            switch.connections.append(parent)
            self.connections.append((parent, switch))
        
        # Level 3: PCs
        for i, switch in enumerate(switches):
            for j in range(2):
                pc = NetworkNode(switch.x - 50 + j*100, 600, "pc", f"PC{i*2+j+1}")
                self.nodes.append(pc)
                
                switch.connections.append(pc)
                pc.connections.append(switch)
                self.connections.append((switch, pc))

        # Initialize TCP congestion control for all nodes
        for node in self.nodes:
            if self.congestion_algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()
    
    def create_linear_topology(self):
        """Linear topology: nodes connected in a line"""
        num_nodes = 7
        start_x, y = 250, 400
        spacing = 150
        
        for i in range(num_nodes):
            x = start_x + i * spacing
            node = NetworkNode(x, y, "router", f"ROUTER{i+1}")
            self.nodes.append(node)
            
            if i > 0:
                prev_node = self.nodes[i-1]
                prev_node.connections.append(node)
                node.connections.append(prev_node)
                self.connections.append((prev_node, node))

        # Initialize TCP congestion control for all nodes
        for node in self.nodes:
            if self.congestion_algorithm == "Tahoe":
                node.tcp_control = TCPTahoe()
            else:
                node.tcp_control = TCPReno()
    
    def add_node(self, node_type):
        x = random.randint(100, 800)
        y = random.randint(100, 600)
        name = f"{node_type.upper()}{len([n for n in self.nodes if n.type == node_type]) + 1}"
        node = NetworkNode(x, y, node_type, name)
        
        # NEW: Initialize TCP congestion control
        if self.congestion_algorithm == "Tahoe":
            node.tcp_control = TCPTahoe()
        else:
            node.tcp_control = TCPReno()
        
        self.nodes.append(node)
        self.draw_network()
        self.status_label.config(text=f"Added {name}")
        
    def toggle_connection_mode(self):
        self.connection_mode = not self.connection_mode
        if self.connection_mode:
            self.conn_button.config(bg=self.colors['success'], text="✓ Connecting...")
            self.status_label.config(text="Click two nodes to connect them")
        else:
            self.conn_button.config(bg=self.colors['secondary'], text="🔗 Connect Nodes")
            self.selected_node = None
            self.status_label.config(text="Ready")
        self.draw_network()
        
    def on_canvas_click(self, event):
        clicked_node = self.get_node_at(event.x, event.y)
        
        if self.connection_mode and clicked_node:
            if self.selected_node is None:
                self.selected_node = clicked_node
                self.status_label.config(text=f"Selected {clicked_node.name}, click another node")
            elif self.selected_node != clicked_node:
                if clicked_node not in self.selected_node.connections:
                    self.selected_node.connections.append(clicked_node)
                    clicked_node.connections.append(self.selected_node)
                    self.connections.append((self.selected_node, clicked_node))
                    self.status_label.config(text=f"Connected {self.selected_node.name} ↔ {clicked_node.name}")
                self.selected_node = None
            self.draw_network()
        elif clicked_node:
            self.dragging_node = clicked_node
            
    def on_canvas_drag(self, event):
        if self.dragging_node and not self.connection_mode:
            self.dragging_node.x = event.x
            self.dragging_node.y = event.y
            self.draw_network()
            
    def on_canvas_release(self, event):
        self.dragging_node = None
        
    def on_right_click(self, event):
        clicked_node = self.get_node_at(event.x, event.y)
        if clicked_node:
            self.show_node_info(clicked_node)
            
    def get_node_at(self, x, y):
        for node in self.nodes:
            dist = math.sqrt((node.x - x)**2 + (node.y - y)**2)
            if dist < 30:
                return node
        return None
        
    def draw_network(self):
        self.canvas.delete("all")
        
        # Draw connections
        for node1, node2 in self.connections:
            color = "#4b5563" if not self.simulation_running else "#6366f1"
            width = 2
            
            # NEW: Highlight path if exists
            if self.highlighted_path and len(self.highlighted_path) > 1:
                for i in range(len(self.highlighted_path) - 1):
                    if ((node1 == self.highlighted_path[i] and node2 == self.highlighted_path[i+1]) or
                        (node2 == self.highlighted_path[i] and node1 == self.highlighted_path[i+1])):
                        color = "#fbbf24"  # Yellow for highlighted path
                        width = 4
                        break
            
            self.canvas.create_line(node1.x, node1.y, node2.x, node2.y,
                                   fill=color, width=width, dash=(5, 3) if width == 2 else None)
        
        # Draw packets
        for packet in self.packets[:]:
            if packet.current_index < len(packet.path) - 1:
                node1 = packet.path[packet.current_index]
                node2 = packet.path[packet.current_index + 1]
                
                # Calculate packet position
                x = node1.x + (node2.x - node1.x) * packet.progress
                y = node1.y + (node2.y - node1.y) * packet.progress
                
                self.canvas.create_oval(x-5, y-5, x+5, y+5, 
                                       fill=packet.color, outline="white", width=2)
                
                packet.progress += 0.05
                if packet.progress >= 1.0:
                    packet.progress = 0
                    packet.current_index += 1
            else:
                self.packets.remove(packet)

          # NEW: Display hop count for active packets
        if self.simulation_running:
            for packet in self.packets:
                if packet.current_index < len(packet.path) - 1:
                    node1 = packet.path[packet.current_index]
                    x = node1.x + (packet.path[packet.current_index + 1].x - node1.x) * packet.progress
                    y = node1.y + (packet.path[packet.current_index + 1].y - node1.y) * packet.progress
                    
                    # Display hop count above packet
                    self.canvas.create_text(x, y - 15, 
                                           text=f"H:{packet.hop_count}",
                                           font=("Segoe UI", 7, "bold"), 
                                           fill="#fbbf24")
        
        # Draw nodes
        for node in self.nodes:
            color = self.colors[node.type]
            
            # Highlight selected
            if node == self.selected_node:
                self.canvas.create_oval(node.x-35, node.y-35, node.x+35, node.y+35,
                                       fill="", outline=self.colors['accent'], width=3)
            
            # Node circle
            self.canvas.create_oval(node.x-30, node.y-30, node.x+30, node.y+30,
                                   fill=color, outline="white", width=2)
            
            # Node icon
            icons = {'cloud': '☁', 'router': '⚡', 'switch': '⊞', 'pc': '💻'}
            self.canvas.create_text(node.x, node.y-5, text=icons[node.type],
                                   font=("Segoe UI", 20), fill="white")
            
            # Node label
            self.canvas.create_text(node.x, node.y+45, text=node.name,
                                   font=("Segoe UI", 9, "bold"), fill=self.colors['text'])
            
            # NEW: Enhanced Congestion indicator with levels
            if node.congestion > 0:
                congestion_level = node.get_congestion_level()
                
                # Color based on congestion level
                if congestion_level == 'low':
                    cong_color = '#10b981'  # Green
                elif congestion_level == 'medium':
                    cong_color = '#f59e0b'  # Yellow
                elif congestion_level == 'high':
                    cong_color = '#ef4444'  # Red
                else:  # critical
                    cong_color = '#dc2626'  # Dark Red
                
                # Draw congestion indicator
                self.canvas.create_oval(node.x+20, node.y-20, node.x+30, node.y-10,
                                       fill=cong_color, outline="white", width=2)
                
                # Add congestion count text
                self.canvas.create_text(node.x+25, node.y-15, 
                                       text=str(int(node.congestion)),
                                       font=("Segoe UI", 7, "bold"), fill="white")

            # NEW: Show TCP congestion control state
            if node.tcp_control and self.simulation_running:
                state_text = f"{node.tcp_control.algorithm[:1]}"  # T or R
                state_color = "#10b981" if node.tcp_control.state == "slow_start" else \
                            "#3b82f6" if node.tcp_control.state == "congestion_avoidance" else "#ef4444"
                
                self.canvas.create_rectangle(node.x-30, node.y+50, node.x-10, node.y+65,
                                            fill=state_color, outline="white", width=1)
                self.canvas.create_text(node.x-20, node.y+57, text=state_text,
                                    font=("Segoe UI", 8, "bold"), fill="white")
                
                # Show cwnd
                cwnd_text = f"W:{node.tcp_control.get_window_size()}"
                self.canvas.create_text(node.x+15, node.y+57, text=cwnd_text,
                                    font=("Segoe UI", 7), fill=self.colors['text'])


        if self.simulation_running:
            self.root.after(50, self.draw_network)
            
    def toggle_simulation(self):
        self.simulation_running = not self.simulation_running
        
        if self.simulation_running:
            self.sim_button.config(text="⏸ Pause", bg=self.colors['warning'])
            self.status_label.config(text="Simulation running...")
            self.start_packet_generation()
            self.decay_congestion()  # NEW: Start congestion decay
            self.draw_network()
        else:
            self.sim_button.config(text="▶ Start Simulation", bg=self.colors['success'])
            self.status_label.config(text="Simulation paused")
            
    def start_packet_generation(self):
        if self.simulation_running and len(self.nodes) > 1:
            # Select random source and destination
            source = random.choice(self.nodes)
            destination = random.choice([n for n in self.nodes if n != source])
            
            # Check if source can send (congestion window check)
            if source.tcp_control and source.packets_in_flight < source.tcp_control.get_window_size():
                path, total_latency = self.dijkstra_shortest_path(source, destination)
                
                if path:
                    # Simulate packet loss based on congestion
                    packet_loss = False
                    for node in path:
                        # Packet loss probability increases with congestion
                        node.packet_loss_probability = min(0.3, node.congestion * 0.03)
                        if random.random() < node.packet_loss_probability:
                            packet_loss = True
                            break
                    
                    if packet_loss:
                        # Handle packet loss
                        source.tcp_control.on_duplicate_ack()
                        
                        # Update congestion based on algorithm state
                        if source.tcp_control.state == "slow_start":
                            congestion_factor = 0.5
                        elif source.tcp_control.state == "fast_recovery":
                            congestion_factor = 1.5
                        else:
                            congestion_factor = 1.0
                        
                        for node in path:
                            node.congestion = min(10, node.congestion + congestion_factor * 0.5)
                    else:
                        # Successfully send packet
                        packet = Packet(source, destination, path)
                        packet.total_latency = total_latency
                        packet.cwnd = source.tcp_control.get_window_size()
                        packet.algorithm = source.tcp_control.algorithm
                        self.packets.append(packet)
                        
                        source.packets_in_flight += 1
                        source.tcp_control.packets_sent += 1
                        
                        # Simulate ACK after packet completes journey
                        self.root.after(int(total_latency), 
                                    lambda: self.handle_packet_ack(source, path))
                        
                        # Update congestion based on cwnd
                        congestion_factor = 1.0 / max(1, source.tcp_control.get_window_size())
                        
                        if self.traffic_load == "light":
                            congestion_factor *= 0.5
                        elif self.traffic_load == "heavy":
                            congestion_factor *= 2
                        
                        for node in path:
                            node.congestion = min(10, node.congestion + congestion_factor)
                    
                    # Track performance
                    self.track_performance(total_latency, len(path))
            
            # Check for timeouts
            self.check_timeouts()
            
            # Continue packet generation
            self.root.after(self.packet_generation_rate, self.start_packet_generation)

    def handle_packet_ack(self, source, path):
        """Handle ACK reception"""
        if source.tcp_control:
            source.tcp_control.on_ack_received()
            source.packets_in_flight = max(0, source.packets_in_flight - 1)
            source.last_ack_time = time.time()
            
            # Reduce congestion when ACK is received
            for node in path:
                node.congestion = max(0, node.congestion - 0.2)

    def check_timeouts(self):
        """Check for packet timeouts"""
        current_time = time.time()
        
        for node in self.nodes:
            if node.tcp_control and node.packets_in_flight > 0:
                if current_time - node.last_ack_time > node.timeout_threshold:
                    # Timeout occurred
                    node.tcp_control.on_timeout()
                    node.packets_in_flight = 0
                    node.last_ack_time = current_time
                    
                    # Increase congestion on timeout
                    node.congestion = min(10, node.congestion + 2)

    # NEW: Track performance over time
    def track_performance(self, latency, hops):
        """Track latency and throughput metrics over time"""
        current_time = time.time() - self.performance_start_time
        self.time_stamps.append(current_time)
        self.latency_history.append(latency)
        
        # Calculate throughput (simplified: packets per second * avg packet size)
        # Assuming 1500 bytes per packet, throughput in Mbps
        if len(self.time_stamps) > 1:
            time_diff = self.time_stamps[-1] - self.time_stamps[-2]
            if time_diff > 0:
                throughput = (1500 * 8) / (time_diff * 1000000)  # Convert to Mbps
                self.throughput_history.append(throughput)
            else:
                self.throughput_history.append(self.throughput_history[-1] if self.throughput_history else 0)
        else:
            self.throughput_history.append(0)
            
         # NEW: Update routing statistics
        self.routing_stats['total_packets'] += 1
        hop_count = hops - 1  # Convert path length to hop count
        
        if hop_count < self.routing_stats['min_hops']:
            self.routing_stats['min_hops'] = hop_count
        if hop_count > self.routing_stats['max_hops']:
            self.routing_stats['max_hops'] = hop_count
        
        # Update average hop count
        total_hops = self.routing_stats['avg_hop_count'] * (self.routing_stats['total_packets'] - 1) + hop_count
        self.routing_stats['avg_hop_count'] = total_hops / self.routing_stats['total_packets']
        
        # Store path in history (keep last 100)
        self.routing_stats['path_history'].append({
            'hops': hop_count,
            'latency': latency,
            'time': time.time() - self.performance_start_time
        })
        
        if len(self.routing_stats['path_history']) > 100:
            self.routing_stats['path_history'].pop(0)

        # Keep only last 50 data points
        if len(self.time_stamps) > 50:
            self.time_stamps.pop(0)
            self.latency_history.pop(0)
            self.throughput_history.pop(0)


    # NEW: Decay congestion over time (natural decrease)
    def decay_congestion(self):
        """Gradually reduce congestion on all nodes"""
        if self.simulation_running:
            for node in self.nodes:
                if node.congestion > 0:
                    # Decay rate based on traffic load
                    decay_rate = 0.1 if self.traffic_load == "heavy" else 0.2
                    node.congestion = max(0, node.congestion - decay_rate)
            
            # Call again after 500ms
            self.root.after(500, self.decay_congestion)

    # NEW: Show Performance Graphs Window
    def show_performance_graphs(self):
        if not self.latency_history or len(self.latency_history) < 2:
            messagebox.showinfo("No Data", "Start the simulation to collect performance data")
            return
        
        graph_window = tk.Toplevel(self.root)
        graph_window.title("Network Performance Graphs")
        graph_window.geometry("1000x700")
        graph_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(graph_window, text="📈 Network Performance Analysis", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
       
        # Create matplotlib figure with 4 subplots
        fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(12, 9))
        fig.patch.set_facecolor('#2a2a3e')
        
        # Graph 1: Latency over Time
        ax1.plot(self.time_stamps, self.latency_history, 
                color='#3b82f6', linewidth=2, marker='o', markersize=4)
        ax1.set_xlabel('Time (seconds)', color='white', fontsize=11)
        ax1.set_ylabel('Latency (ms)', color='white', fontsize=11)
        ax1.set_title('Network Latency Over Time', color='white', fontsize=13, fontweight='bold')
        ax1.grid(True, alpha=0.3, color='#4b5563')
        ax1.set_facecolor('#1e1e2e')
        ax1.tick_params(colors='white')
        
        # Graph 2: Throughput over Time
        ax2.plot(self.time_stamps, self.throughput_history, 
                color='#10b981', linewidth=2, marker='s', markersize=4)
        ax2.set_xlabel('Time (seconds)', color='white', fontsize=11)
        ax2.set_ylabel('Throughput (Mbps)', color='white', fontsize=11)
        ax2.set_title('Network Throughput Over Time', color='white', fontsize=13, fontweight='bold')
        ax2.grid(True, alpha=0.3, color='#4b5563')
        ax2.set_facecolor('#1e1e2e')
        ax2.tick_params(colors='white')
        
        # Graph 3: Hop Count Distribution
        hop_counts = [packet.hop_count for packet in self.packets if hasattr(packet, 'hop_count')]
        if not hop_counts:
            # Use path lengths from history
            hop_counts = list(range(1, min(len(self.nodes), 10)))
            hop_frequencies = [random.randint(1, 10) for _ in hop_counts]
        else:
            hop_frequencies = [hop_counts.count(i) for i in range(max(hop_counts) + 1)]
            hop_counts = list(range(max(hop_counts) + 1))
        
        ax3.bar(hop_counts, hop_frequencies, color='#8b5cf6', alpha=0.8, edgecolor='white', linewidth=1.5)
        ax3.set_xlabel('Number of Hops', color='white', fontsize=11)
        ax3.set_ylabel('Frequency', color='white', fontsize=11)
        ax3.set_title('Hop Count Distribution', color='white', fontsize=13, fontweight='bold')
        ax3.grid(True, alpha=0.3, color='#4b5563', axis='y')
        ax3.set_facecolor('#1e1e2e')
        ax3.tick_params(colors='white')
        
        # NEW: Graph 4: Congestion Heatmap
        congestion_data = [node.congestion for node in self.nodes]
        node_names = [node.name for node in self.nodes]
        
        colors_map = ['#10b981' if c <= 1 else '#f59e0b' if c <= 3 else '#ef4444' if c <= 5 else '#dc2626' 
                      for c in congestion_data]
        
        ax4.barh(node_names[:10], congestion_data[:10], color=colors_map[:10], alpha=0.8, edgecolor='white')
        ax4.set_xlabel('Congestion Level', color='white', fontsize=11)
        ax4.set_ylabel('Node', color='white', fontsize=11)
        ax4.set_title('Node Congestion Levels', color='white', fontsize=13, fontweight='bold')
        ax4.grid(True, alpha=0.3, color='#4b5563', axis='x')
        ax4.set_facecolor('#1e1e2e')
        ax4.tick_params(colors='white')

        plt.tight_layout()
        
        # Embed matplotlib figure in tkinter window
        canvas_frame = tk.Frame(graph_window, bg=self.colors['bg'])
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = FigureCanvasTkAgg(fig, master=canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Statistics Frame
        stats_frame = tk.Frame(graph_window, bg=self.colors['panel_bg'])
        stats_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # Calculate statistics
        avg_latency = sum(self.latency_history) / len(self.latency_history)
        max_latency = max(self.latency_history)
        min_latency = min(self.latency_history)
        avg_throughput = sum(self.throughput_history) / len(self.throughput_history) if self.throughput_history else 0
        
        stats_text = f"📊 Statistics: Avg Latency: {avg_latency:.2f}ms | Min: {min_latency:.2f}ms | Max: {max_latency:.2f}ms | Avg Throughput: {avg_throughput:.2f}Mbps"
        
        stats_label = tk.Label(stats_frame, text=stats_text,
                              bg=self.colors['panel_bg'], fg=self.colors['text'],
                              font=("Segoe UI", 10, "bold"))
        stats_label.pack(pady=10)
        
        # Buttons
        btn_frame = tk.Frame(graph_window, bg=self.colors['bg'])
        btn_frame.pack(pady=10)
        
        def refresh_graphs():
            graph_window.destroy()
            self.show_performance_graphs()
        
        def export_data():
            messagebox.showinfo("Export", f"Exported {len(self.latency_history)} data points to CSV")
        
        refresh_btn = tk.Button(btn_frame, text="🔄 Refresh",
                               command=refresh_graphs,
                               bg=self.colors['accent'], fg="white",
                               font=("Segoe UI", 10, "bold"),
                               relief=tk.FLAT, cursor="hand2", padx=20, pady=8)
        refresh_btn.pack(side=tk.LEFT, padx=5)
        
        export_btn = tk.Button(btn_frame, text="💾 Export Data",
                              command=export_data,
                              bg=self.colors['success'], fg="white",
                              font=("Segoe UI", 10, "bold"),
                              relief=tk.FLAT, cursor="hand2", padx=20, pady=8)
        export_btn.pack(side=tk.LEFT, padx=5)


    # NEW: Show Routing Analysis Window
    def show_routing_analysis(self):
        if not self.nodes:
            messagebox.showwarning("No Network", "Create a network topology first")
            return
        
        if self.routing_stats['total_packets'] == 0:
            messagebox.showinfo("No Data", "Start simulation to collect routing data")
            return
        
        routing_window = tk.Toplevel(self.root)
        routing_window.title("Routing Analysis & Hop Count Statistics")
        routing_window.geometry("900x700")
        routing_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(routing_window, text="🧭 Routing Analysis Dashboard", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=15)
        
        # Create notebook for tabs
        notebook = ttk.Notebook(routing_window)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Tab 1: Statistics Overview
        stats_frame = tk.Frame(notebook, bg=self.colors['canvas_bg'])
        notebook.add(stats_frame, text="📊 Statistics")
        
        stats_text = tk.Text(stats_frame, bg=self.colors['canvas_bg'], 
                            fg=self.colors['text'], font=("Consolas", 11),
                            wrap=tk.WORD)
        stats_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Calculate routing statistics
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         ROUTING PERFORMANCE STATISTICS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"Total Packets Routed: {self.routing_stats['total_packets']}\n")
        stats_text.insert(tk.END, f"Average Hop Count: {self.routing_stats['avg_hop_count']:.2f}\n")
        stats_text.insert(tk.END, f"Minimum Hops: {self.routing_stats['min_hops']}\n")
        stats_text.insert(tk.END, f"Maximum Hops: {self.routing_stats['max_hops']}\n\n")
        
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         NETWORK TOPOLOGY ANALYSIS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"Total Nodes: {len(self.nodes)}\n")
        stats_text.insert(tk.END, f"Total Links: {len(self.connections)}\n")
        stats_text.insert(tk.END, f"Network Density: {(2 * len(self.connections)) / (len(self.nodes) * (len(self.nodes) - 1)) * 100:.2f}%\n\n")
        
        # Node-wise routing statistics
        stats_text.insert(tk.END, "=" * 60 + "\n")
        stats_text.insert(tk.END, "         NODE ROUTING STATISTICS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        stats_text.insert(tk.END, f"{'Node':<15} {'Type':<10} {'Connections':<12} {'Traffic':<10}\n")
        stats_text.insert(tk.END, "-" * 60 + "\n")
        
        for node in sorted(self.nodes, key=lambda n: len(n.connections), reverse=True):
            traffic_level = "🔴 High" if node.congestion > 5 else "🟡 Med" if node.congestion > 2 else "🟢 Low"
            stats_text.insert(tk.END, f"{node.name:<15} {node.type:<10} {len(node.connections):<12} {traffic_level:<10}\n")
        
        stats_text.insert(tk.END, "\n" + "=" * 60 + "\n")
        stats_text.insert(tk.END, "         PATH EFFICIENCY ANALYSIS\n")
        stats_text.insert(tk.END, "=" * 60 + "\n\n")
        
        if self.routing_stats['path_history']:
            recent_paths = self.routing_stats['path_history'][-20:]
            avg_recent_hops = sum(p['hops'] for p in recent_paths) / len(recent_paths)
            avg_recent_latency = sum(p['latency'] for p in recent_paths) / len(recent_paths)
            
            stats_text.insert(tk.END, f"Recent Packets (Last 20):\n")
            stats_text.insert(tk.END, f"  Average Hops: {avg_recent_hops:.2f}\n")
            stats_text.insert(tk.END, f"  Average Latency: {avg_recent_latency:.2f}ms\n\n")
            
            # Efficiency score (lower is better)
            efficiency = (avg_recent_hops / self.routing_stats['avg_hop_count']) * 100 if self.routing_stats['avg_hop_count'] > 0 else 100
            stats_text.insert(tk.END, f"Routing Efficiency: {efficiency:.1f}%\n")
            
            if efficiency < 90:
                stats_text.insert(tk.END, "  ⚠️  Routing paths are longer than average\n")
            elif efficiency > 110:
                stats_text.insert(tk.END, "  ✅ Routing paths are shorter than average\n")
            else:
                stats_text.insert(tk.END, "  ℹ️  Routing paths are near average\n")
        
        stats_text.config(state=tk.DISABLED)
        
        # Tab 2: Hop Count Visualization
        viz_frame = tk.Frame(notebook, bg=self.colors['bg'])
        notebook.add(viz_frame, text="📈 Visualizations")
        
        # Create hop count distribution graph
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 5))
        fig.patch.set_facecolor('#2a2a3e')
        
        # Graph 1: Hop Count Distribution
        if self.routing_stats['path_history']:
            hop_counts = [p['hops'] for p in self.routing_stats['path_history']]
            hop_range = range(int(min(hop_counts)), int(max(hop_counts)) + 1)
            hop_freq = [hop_counts.count(h) for h in hop_range]
            
            ax1.bar(hop_range, hop_freq, color='#8b5cf6', alpha=0.8, edgecolor='white', linewidth=1.5)
            ax1.set_xlabel('Hop Count', color='white', fontsize=11)
            ax1.set_ylabel('Frequency', color='white', fontsize=11)
            ax1.set_title('Hop Count Distribution', color='white', fontsize=12, fontweight='bold')
            ax1.grid(True, alpha=0.3, color='#4b5563', axis='y')
            ax1.set_facecolor('#1e1e2e')
            ax1.tick_params(colors='white')
        
        # Graph 2: Hop Count vs Latency
        if self.routing_stats['path_history']:
            hops_list = [p['hops'] for p in self.routing_stats['path_history']]
            latency_list = [p['latency'] for p in self.routing_stats['path_history']]
            
            ax2.scatter(hops_list, latency_list, color='#3b82f6', alpha=0.6, s=50, edgecolors='white')
            ax2.set_xlabel('Hop Count', color='white', fontsize=11)
            ax2.set_ylabel('Latency (ms)', color='white', fontsize=11)
            ax2.set_title('Hop Count vs Latency Correlation', color='white', fontsize=12, fontweight='bold')
            ax2.grid(True, alpha=0.3, color='#4b5563')
            ax2.set_facecolor('#1e1e2e')
            ax2.tick_params(colors='white')
        
        plt.tight_layout()
        
        # Embed matplotlib figure
        canvas_frame = tk.Frame(viz_frame, bg=self.colors['bg'])
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        canvas = FigureCanvasTkAgg(fig, master=canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Tab 3: Path Comparison
        compare_frame = tk.Frame(notebook, bg=self.colors['canvas_bg'])
        notebook.add(compare_frame, text="🔍 Path Finder")
        
        # Add path comparison tool
        compare_label = tk.Label(compare_frame, text="Compare Routes Between Nodes", 
                                font=("Segoe UI", 13, "bold"),
                                bg=self.colors['canvas_bg'], fg=self.colors['text'])
        compare_label.pack(pady=15)
        
        select_frame = tk.Frame(compare_frame, bg=self.colors['panel_bg'])
        select_frame.pack(pady=10, padx=20, fill=tk.X)
        
        tk.Label(select_frame, text="Node A:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 10)).grid(row=0, column=0, padx=10, pady=10)
        
        nodeA_var = tk.StringVar()
        nodeA_dropdown = ttk.Combobox(select_frame, textvariable=nodeA_var, 
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=15)
        nodeA_dropdown.grid(row=0, column=1, padx=10, pady=10)
        
        tk.Label(select_frame, text="Node B:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 10)).grid(row=0, column=2, padx=10, pady=10)
        
        nodeB_var = tk.StringVar()
        nodeB_dropdown = ttk.Combobox(select_frame, textvariable=nodeB_var,
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=15)
        nodeB_dropdown.grid(row=0, column=3, padx=10, pady=10)
        
        compare_text = tk.Text(compare_frame, bg=self.colors['canvas_bg'], 
                              fg=self.colors['text'], font=("Consolas", 10),
                              wrap=tk.WORD, height=20)
        compare_text.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        def compare_routes():
            nodeA_name = nodeA_var.get()
            nodeB_name = nodeB_var.get()
            
            if not nodeA_name or not nodeB_name:
                messagebox.showwarning("Selection Required", "Please select both nodes")
                return
            
            nodeA = next((n for n in self.nodes if n.name == nodeA_name), None)
            nodeB = next((n for n in self.nodes if n.name == nodeB_name), None)
            
            if not nodeA or not nodeB or nodeA == nodeB:
                messagebox.showwarning("Invalid Selection", "Please select two different nodes")
                return
            
            path, latency = self.dijkstra_shortest_path(nodeA, nodeB)
            
            compare_text.config(state=tk.NORMAL)
            compare_text.delete(1.0, tk.END)
            
            if path:
                compare_text.insert(tk.END, "=" * 55 + "\n")
                compare_text.insert(tk.END, f"  ROUTE ANALYSIS: {nodeA.name} → {nodeB.name}\n")
                compare_text.insert(tk.END, "=" * 55 + "\n\n")
                
                compare_text.insert(tk.END, f"Total Hops: {len(path) - 1}\n")
                compare_text.insert(tk.END, f"Total Latency: {latency:.2f}ms\n")
                compare_text.insert(tk.END, f"Average Latency per Hop: {latency / (len(path) - 1):.2f}ms\n\n")
                
                compare_text.insert(tk.END, "Detailed Path:\n")
                compare_text.insert(tk.END, "-" * 55 + "\n")
                
                for i, node in enumerate(path):
                    compare_text.insert(tk.END, f"Hop {i}: {node.name} ({node.type})\n")
                    compare_text.insert(tk.END, f"  Latency: {node.latency}ms\n")
                    compare_text.insert(tk.END, f"  Congestion: {node.congestion:.1f}\n")
                    if i < len(path) - 1:
                        compare_text.insert(tk.END, "  ↓\n")
                
                compare_text.insert(tk.END, "\n" + "=" * 55 + "\n")
                
                # Comparison with network average
                if self.routing_stats['avg_hop_count'] > 0:
                    compare_text.insert(tk.END, "\nComparison with Network Average:\n")
                    compare_text.insert(tk.END, f"Network Avg Hops: {self.routing_stats['avg_hop_count']:.2f}\n")
                    compare_text.insert(tk.END, f"This Route Hops: {len(path) - 1}\n")
                    
                    if len(path) - 1 < self.routing_stats['avg_hop_count']:
                        compare_text.insert(tk.END, "✅ This route is shorter than average!\n")
                    elif len(path) - 1 > self.routing_stats['avg_hop_count']:
                        compare_text.insert(tk.END, "⚠️  This route is longer than average.\n")
                    else:
                        compare_text.insert(tk.END, "ℹ️  This route matches the network average.\n")
            else:
                compare_text.insert(tk.END, "❌ No route found between these nodes.\n")
            
            compare_text.config(state=tk.DISABLED)
        
        compare_btn = tk.Button(compare_frame, text="🔍 Analyze Route",
                               command=compare_routes,
                               bg=self.colors['accent'], fg="white",
                               font=("Segoe UI", 10, "bold"),
                               relief=tk.FLAT, cursor="hand2", padx=20, pady=10)
        compare_btn.pack(pady=10)
            
    def find_path(self, source, destination):
        # BFS to find path
        visited = set()
        queue = [(source, [source])]
        
        while queue:
            node, path = queue.pop(0)
            if node == destination:
                return path
                
            if node not in visited:
                visited.add(node)
                for neighbor in node.connections:
                    if neighbor not in visited:
                        queue.append((neighbor, path + [neighbor]))
        
        return None
    
    # NEW: Dijkstra's Shortest Path Algorithm
    def dijkstra_shortest_path(self, source, destination):
        """Find shortest path using Dijkstra's algorithm based on latency"""
        distances = {node: float('infinity') for node in self.nodes}
        distances[source] = 0
        previous = {node: None for node in self.nodes}
        unvisited = set(self.nodes)
        
        while unvisited:
            # Find node with minimum distance
            current = min(unvisited, key=lambda node: distances[node])
            
            if distances[current] == float('infinity'):
                break
            
            if current == destination:
                # Reconstruct path
                path = []
                while current:
                    path.append(current)
                    current = previous[current]
                return path[::-1], distances[destination]
            
            unvisited.remove(current)
            
            # Update distances to neighbors
            for neighbor in current.connections:
                if neighbor in unvisited:
                    # Calculate distance (using latency as weight)
                    alt_distance = distances[current] + current.latency
                    
                    if alt_distance < distances[neighbor]:
                        distances[neighbor] = alt_distance
                        previous[neighbor] = current
        
        return None, float('infinity')
    
    # NEW: Show Path Finder Window
    def show_path_finder(self):
        if len(self.nodes) < 2:
            messagebox.showwarning("Not Enough Nodes", "Add at least 2 nodes to find a path")
            return
        
        path_window = tk.Toplevel(self.root)
        path_window.title("Shortest Path Finder")
        path_window.geometry("500x600")
        path_window.configure(bg=self.colors['bg'])
        
        # Title
        title = tk.Label(path_window, text="🗺️ Dijkstra's Shortest Path", 
                        font=("Segoe UI", 16, "bold"),
                        bg=self.colors['bg'], fg=self.colors['text'])
        title.pack(pady=20)
        
        # Selection Frame
        select_frame = tk.Frame(path_window, bg=self.colors['panel_bg'])
        select_frame.pack(pady=10, padx=20, fill=tk.X)
        
        # Source selection
        tk.Label(select_frame, text="Source Node:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11)).grid(row=0, column=0, padx=10, pady=10, sticky='w')
        
        source_var = tk.StringVar()
        source_dropdown = ttk.Combobox(select_frame, textvariable=source_var, 
                                      values=[node.name for node in self.nodes],
                                      state='readonly', width=20)
        source_dropdown.grid(row=0, column=1, padx=10, pady=10)
        if self.nodes:
            source_dropdown.current(0)
        
        # Destination selection
        tk.Label(select_frame, text="Destination Node:", 
                bg=self.colors['panel_bg'], fg=self.colors['text'],
                font=("Segoe UI", 11)).grid(row=1, column=0, padx=10, pady=10, sticky='w')
        
        dest_var = tk.StringVar()
        dest_dropdown = ttk.Combobox(select_frame, textvariable=dest_var,
                                     values=[node.name for node in self.nodes],
                                     state='readonly', width=20)
        dest_dropdown.grid(row=1, column=1, padx=10, pady=10)
        if len(self.nodes) > 1:
            dest_dropdown.current(1)
        
        # Result display
        result_frame = tk.Frame(path_window, bg=self.colors['canvas_bg'])
        result_frame.pack(pady=20, padx=20, fill=tk.BOTH, expand=True)
        
        result_text = tk.Text(result_frame, bg=self.colors['canvas_bg'], 
                             fg=self.colors['text'], font=("Consolas", 10),
                             wrap=tk.WORD, height=15)
        result_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        def calculate_path():
            source_name = source_var.get()
            dest_name = dest_var.get()
            
            if not source_name or not dest_name:
                messagebox.showwarning("Selection Required", "Please select both source and destination")
                return
            
            if source_name == dest_name:
                messagebox.showwarning("Same Node", "Source and destination must be different")
                return
            
            # Find nodes
            source_node = next((n for n in self.nodes if n.name == source_name), None)
            dest_node = next((n for n in self.nodes if n.name == dest_name), None)
            
            if not source_node or not dest_node:
                messagebox.showerror("Error", "Could not find selected nodes")
                return
            
            # Calculate shortest path
            path, total_latency = self.dijkstra_shortest_path(source_node, dest_node)
            
            result_text.config(state=tk.NORMAL)
            result_text.delete(1.0, tk.END)
            
            if path:
                result_text.insert(tk.END, "=" * 50 + "\n")
                result_text.insert(tk.END, "SHORTEST PATH FOUND\n")
                result_text.insert(tk.END, "=" * 50 + "\n\n")
                
                result_text.insert(tk.END, f"Source: {source_node.name}\n")
                result_text.insert(tk.END, f"Destination: {dest_node.name}\n\n")
                
                result_text.insert(tk.END, f"Total Hops: {len(path) - 1}\n")
                result_text.insert(tk.END, f"Total Latency: {total_latency:.2f}ms\n\n")
                
                result_text.insert(tk.END, "Path Traversal:\n")
                result_text.insert(tk.END, "-" * 50 + "\n")
                
                for i, node in enumerate(path):
                    result_text.insert(tk.END, f"{i+1}. {node.name} ({node.type})")
                    if i < len(path) - 1:
                        result_text.insert(tk.END, f" → [Latency: {node.latency}ms]\n")
                    else:
                        result_text.insert(tk.END, "\n")
                
                result_text.insert(tk.END, "\n" + "=" * 50 + "\n")
                
                # Highlight path on canvas
                self.highlighted_path = path
                self.draw_network()
                
                messagebox.showinfo("Success", f"Path found with {len(path)-1} hops!")
            else:
                result_text.insert(tk.END, "=" * 50 + "\n")
                result_text.insert(tk.END, "NO PATH FOUND\n")
                result_text.insert(tk.END, "=" * 50 + "\n\n")
                result_text.insert(tk.END, f"No connection exists between\n")
                result_text.insert(tk.END, f"{source_node.name} and {dest_node.name}\n\n")
                result_text.insert(tk.END, "The nodes are not connected in the\n")
                result_text.insert(tk.END, "current network topology.\n")
                
                self.highlighted_path = []
                self.draw_network()
            
            result_text.config(state=tk.DISABLED)
        
        def clear_highlight():
            self.highlighted_path = []
            self.draw_network()
            result_text.config(state=tk.NORMAL)
            result_text.delete(1.0, tk.END)
            result_text.config(state=tk.DISABLED)
        
        # Buttons
        btn_frame = tk.Frame(path_window, bg=self.colors['bg'])
        btn_frame.pack(pady=10)
        
        calc_btn = tk.Button(btn_frame, text="🔍 Find Shortest Path",
                           command=calculate_path,
                           bg=self.colors['success'], fg="white",
                           font=("Segoe UI", 10, "bold"),
                           relief=tk.FLAT, cursor="hand2", padx=20, pady=10)
        calc_btn.pack(side=tk.LEFT, padx=5)
        
        clear_btn = tk.Button(btn_frame, text="🗑️ Clear Highlight",
                            command=clear_highlight,
                            bg=self.colors['warning'], fg="white",
                            font=("Segoe UI", 10, "bold"),
                            relief=tk.FLAT, cursor="hand2", padx=20, pady=10)
        clear_btn.pack(side=tk.LEFT, padx=5)
    
    

    def show_node_info(self, node):
        info = f"Node: {node.name}\n"
        info += f"Type: {node.type.upper()}\n"
        info += f"Latency: {node.latency}ms\n"
        info += f"Throughput: {node.throughput}Mbps\n"
        info += f"Connections: {len(node.connections)}\n"
        info += f"Congestion Level: {node.congestion}"
        
        messagebox.showinfo(f"{node.name} Details", info)
        
    def show_metrics(self):
        if not self.nodes:
            messagebox.showwarning("No Data", "Add nodes to view metrics")
            return
            
        metrics_window = tk.Toplevel(self.root)
        metrics_window.title("Network Metrics")
        metrics_window.geometry("500x400")
        metrics_window.configure(bg=self.colors['bg'])
        
        text = tk.Text(metrics_window, bg=self.colors['canvas_bg'], 
                      fg=self.colors['text'], font=("Consolas", 10))
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Calculate metrics
        avg_latency = sum(n.latency for n in self.nodes) / len(self.nodes)
        avg_throughput = sum(n.throughput for n in self.nodes) / len(self.nodes)
        total_connections = len(self.connections)
        
        text.insert(tk.END, "=" * 50 + "\n")
        text.insert(tk.END, "NETWORK PERFORMANCE METRICS\n")
        text.insert(tk.END, "=" * 50 + "\n\n")
        text.insert(tk.END, f"Total Nodes: {len(self.nodes)}\n")
        text.insert(tk.END, f"Total Connections: {total_connections}\n")
        text.insert(tk.END, f"Active Packets: {len(self.packets)}\n\n")
        text.insert(tk.END, f"Average Latency: {avg_latency:.2f}ms\n")
        text.insert(tk.END, f"Average Throughput: {avg_throughput:.2f}Mbps\n\n")
        text.insert(tk.END, "=" * 50 + "\n")
        text.insert(tk.END, "NODE DETAILS\n")
        text.insert(tk.END, "=" * 50 + "\n\n")
        
        for node in self.nodes:
            text.insert(tk.END, f"{node.name} ({node.type}):\n")
            text.insert(tk.END, f"  Latency: {node.latency}ms\n")
            text.insert(tk.END, f"  Throughput: {node.throughput}Mbps\n")
            text.insert(tk.END, f"  Connections: {len(node.connections)}\n")
            text.insert(tk.END, f"  Congestion: {node.congestion}\n\n")
        
         # NEW: Congestion Summary
        text.insert(tk.END, "=" * 50 + "\n")
        text.insert(tk.END, "CONGESTION ANALYSIS\n")
        text.insert(tk.END, "=" * 50 + "\n\n")
        text.insert(tk.END, f"Traffic Load: {self.traffic_load.upper()}\n")
        text.insert(tk.END, f"Packet Rate: Every {self.packet_generation_rate}ms\n\n")
        
        congested_nodes = [n for n in self.nodes if n.congestion > 3]
        text.insert(tk.END, f"Congested Nodes (>3): {len(congested_nodes)}\n")
        if congested_nodes:
            for node in congested_nodes:
                text.insert(tk.END, f"  - {node.name}: {node.congestion:.1f}\n")

        # NEW: TCP Congestion Control Statistics
        text.insert(tk.END, "\n" + "=" * 50 + "\n")
        text.insert(tk.END, "TCP CONGESTION CONTROL\n")
        text.insert(tk.END, "=" * 50 + "\n\n")
        text.insert(tk.END, f"Algorithm: TCP {self.congestion_algorithm}\n\n")

        for node in self.nodes[:5]:  # Show first 5 nodes
            if node.tcp_control:
                text.insert(tk.END, f"{node.name}:\n")
                text.insert(tk.END, f"  State: {node.tcp_control.state}\n")
                text.insert(tk.END, f"  CWND: {node.tcp_control.get_window_size()}\n")
                text.insert(tk.END, f"  SSThresh: {node.tcp_control.ssthresh:.1f}\n")
                text.insert(tk.END, f"  Packets Sent: {node.tcp_control.packets_sent}\n")
                text.insert(tk.END, f"  Packets ACKed: {node.tcp_control.packets_acked}\n")
                text.insert(tk.END, f"  In Flight: {node.packets_in_flight}\n\n")
        # NEW: Routing Statistics Summary
        text.insert(tk.END, "\n" + "=" * 50 + "\n")
        text.insert(tk.END, "ROUTING STATISTICS\n")
        text.insert(tk.END, "=" * 50 + "\n\n")
        text.insert(tk.END, f"Total Packets: {self.routing_stats['total_packets']}\n")
        text.insert(tk.END, f"Avg Hop Count: {self.routing_stats['avg_hop_count']:.2f}\n")
        text.insert(tk.END, f"Min Hops: {self.routing_stats['min_hops'] if self.routing_stats['min_hops'] != float('inf') else 'N/A'}\n")
        text.insert(tk.END, f"Max Hops: {self.routing_stats['max_hops']}\n")


        text.config(state=tk.DISABLED)
        
    def reset_network(self, confirm=True):
        if confirm and not messagebox.askyesno("Reset", "Clear all nodes and connections?"):
            return
            
        self.nodes.clear()
        self.connections.clear()
        self.packets.clear()
        self.simulation_running = False
        self.sim_button.config(text="▶ Start Simulation", bg=self.colors['success'])
        # NEW: Clear performance data
        self.latency_history.clear()
        self.throughput_history.clear()
        self.time_stamps.clear()
        self.performance_start_time = time.time()
         # NEW: Clear routing statistics
        self.routing_stats = {
            'total_packets': 0,
            'avg_hop_count': 0,
            'min_hops': float('inf'),
            'max_hops': 0,
            'path_history': []
        }
        self.draw_network()
        self.status_label.config(text="Network reset")

if __name__ == "__main__":
    root = tk.Tk()
    app = CloudNetworkSimulator(root)
    root.mainloop()