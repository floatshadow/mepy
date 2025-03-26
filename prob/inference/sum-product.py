import sys
from collections import defaultdict


def post_order_traversal(graph_var, graph_factor, node, is_var, parent, ordering):
  if is_var:
    for child in graph_var[node]:
      if child != parent:
        ordering = post_order_traversal(
          graph_var, graph_factor, child, False, node, ordering 
        )
  else:
    for child in graph_factor[node]:
      if child != parent:
        ordering = post_order_traversal(
          graph_var, graph_factor, child, True, node, ordering
        )
  ordering.append((is_var, node, parent))
  return ordering

def pre_order_traversal(graph_var, graph_factor, node, is_var, parent, ordering):
  ordering.append((is_var, node, parent))
  if is_var:
    for child in graph_var[node]:
      if child != parent:
        ordering = pre_order_traversal(
          graph_var, graph_factor, child, False, node, ordering 
        )
  else:
    for child in graph_factor[node]:
      if child != parent:
        ordering = pre_order_traversal(
          graph_var, graph_factor, child, True, node, ordering
        )
  return ordering

def compute_msg_bottom_up(graph_var, factors, ordering, msgs_v2f, msgs_f2v):
  # message passing bottom up: from leaf to root
  for is_var, node, parent in ordering:
    # root has no parent
    if parent is None:
      continue

    if is_var:
      # message from variable to factor (node -> parent)
      msg = [1.0, 1.0]
      for child in graph_var[node]:
        if child != parent:
          msg_f2v = msgs_f2v[(child, node)]
          msg[0] *= msg_f2v[0]
          msg[1] *= msg_f2v[1]
      # print(f"[1] var {node} -> factor {parent}, {msg}")
      assert len(msgs_v2f[(node, parent)]) == 0
      msgs_v2f[(node, parent)] = msg
    else:
      # message from factor to variable
      #       parent (variable)
      #       |
      #       node (factor)
      #       / | \
      #      other varibales (variable)
      (factor_id, vars, f) = factors[node]
      assert factor_id == node, "inconsistent factor id"
      parent_idx = vars.index(parent)
      msg = [0.0, 0.0]
      ki = len(vars)
      for event in range(1 << ki):
        # decompose the value of x_[1:ki]
        bits = []
        for i in range(ki):
          bits.append((event >> i) & 1)
        
        # the binary string is in reverse order
        bits = list(reversed(bits))
        fv = f[event]
        prod = 1.0
        for i in range(ki):
          if i == parent_idx:
            continue
          var = vars[i]
          msg_v2f = msgs_v2f[(var, node)]
          prod *= msg_v2f[bits[i]]
        # print(f"event {event} comp {fv * prod}, bits {bits} parent_idx {parent_idx} fv {fv}")
        msg[bits[parent_idx]] += fv * prod
      
      # print(f"[1] factor {node} -> var {parent}, {msg}")
      assert len(msgs_f2v[(node, parent)]) == 0
      msgs_f2v[(node, parent)] = msg

def compute_msg_top_down(graph_var, factors, ordering, msgs_v2f, msgs_f2v):
  # message passing top down: from root to leaf
  for is_var, node, parent in ordering:

    if is_var:
      # message from variable to factor (node -> childs)
      # node -> parent has been computed
      #       parent (factor)
      #       |
      #       node (variable)
      #       / | \
      #      other factors (factor)
      for child in graph_var[node]:
        msg = [1.0, 1.0]
        if child != parent:
          for other_factor in graph_var[node]:
            if other_factor != child:
              msg_f2v = msgs_f2v[(other_factor, node)]
              msg[0] *= msg_f2v[0]
              msg[1] *= msg_f2v[1]
          # print(f"[2] var {node} -> factor {child}, {msg}")
          assert len(msgs_v2f[(node, child)]) == 0
          msgs_v2f[(node, child)] = msg
    else:
      # message from factor to variable
      (_, vars, f) = factors[node]
      ki = len(vars)

      for child in vars:
        # compute node -> child
        if child != parent:
          msg = [0.0, 0.0]
          child_idx = vars.index(child)
          for event in range(1 << ki):
            # decompose the value of x_[1:ki]
            bits = []
            for i in range(ki):
              bits.append((event >> i) & 1)
        
            # the binary string is in reverse order
            bits = list(reversed(bits))
            fv = f[event]
            prod = 1.0
            for i in range(ki):
              if i == child_idx:
                continue
              var = vars[i]
              msg_v2f = msgs_v2f[(var, node)]
              prod *= msg_v2f[bits[i]]
            # print(f"event {event} comp {fv * prod}, bits {bits} fv {fv}")
            msg[bits[child_idx]] += fv * prod
      
          # print(f"[2] factor {node} -> var {child}, {msg}")
          assert len(msgs_f2v[(node, child)]) == 0
          msgs_f2v[(node, child)] = msg

if __name__ == "__main__":
  inputs = [line.strip().split() for line in sys.stdin]
  nx, nf = map(int, inputs[0])

  factors = []
  for (id, line) in enumerate(inputs[1:]):
    ki = int(line[0])
    variables = list(map(int, line[1 : ki + 1]))
    factor_f = list(map(float, line[ki + 1 : ]))
    assert len(factor_f) == 1 << ki, "length of factor_f is not 2^ki"
    factors.append((id, variables, factor_f))
    

  graph_var = defaultdict(list)
  graph_factor = defaultdict(list)
  for (factor_id, vars, _) in factors:
    for var in vars:
      graph_var[var].append(factor_id)
      graph_factor[factor_id].append(var)

  # select variable 1 as root
  root = 1
  msgs_v2f = defaultdict(list)
  msgs_f2v = defaultdict(list)
  # Bottom up
  post_ordering = post_order_traversal(graph_var, graph_factor, root, True, None, [])
  compute_msg_bottom_up(graph_var, factors, post_ordering, msgs_v2f, msgs_f2v)
  # Top down
  pre_ordering = pre_order_traversal(graph_var, graph_factor, root, True, None, [])
  compute_msg_top_down(graph_var, factors, pre_ordering, msgs_v2f, msgs_f2v)

  # all messages are ready
  for i in range(1, nx + 1):
    p = [1.0, 1.0]
    neighbor_f = graph_var[i]
    for f in neighbor_f:
      msg = msgs_f2v[(f, i)]
      p[0] *= msg[0]
      p[1] *= msg[1]
    # normalize
    p_sum = p[0] + p[1]
    p[0] /= p_sum
    p[1] /= p_sum
    print(f"{p[0]:.2f} {p[1]:.2f}")


