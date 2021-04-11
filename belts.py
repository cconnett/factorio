import dataclasses
import fractions
import pysmt.shortcuts as s
import pysmt.typing as t


@dataclasses.dataclass
class Belt:
  rho: t.REAL
  v: t.REAL

  @property
  def flux(self):
    return s.Min(self.rho, self.v)


def get_model_or_print_ucore(formula):
  m = s.get_model(formula)
  if not m:
    print('unsat')
    from pysmt.rewritings import conjunctive_partition
    conj = conjunctive_partition(s.And(formula))
    ucore = s.get_unsat_core(conj)
    print("UNSAT-Core size '%d'" % len(ucore))
    for f in ucore:
      print(f.serialize())
    return
  return m


def domain(belt):
  yield 0 <= belt.rho <= 1
  yield 0 <= belt.v <= 1


def balancer_flow_formula(junctions, width, length):
  formula = []
  belts = [[
      Belt(s.Symbol(f'b{i}[{x}].rho', t.REAL), s.Symbol(f'b{i}[{x}].v', t.REAL))
      for x in range(length + 1)
  ]
           for i in range(width)]
  for beltway in belts:
    for belt in beltway:
      formula.extend(domain(belt))
  if not s.is_sat(s.And(formula)):
    raise Exception('Domain is not SAT :/')

  # Balancing rules.
  junctions_by_x = [[] for x in range(length + 1)]
  for (x, y1, y2) in junctions:
    junctions_by_x[x].append((y1, y2))
    inn = x - 1
    out = x

    input_rho = s.Plus(belts[y1][inn].rho, belts[y2][inn].rho)
    # We want to put half of the input on each output.
    half_input = s.Div(input_rho, s.Real(2))

    # If output velocity is less than the half_input that we would like to
    # assign to it, we've filled it. Velocity is a hard limit, because it's out
    # of influence of this splitter. We'll set the output density to 1 in that
    # case. Aside: The flux is the min of that and the velocity, so if
    # out-velocity is the limiting factor, it won't change the flux calculation
    # to just assign rho_out = v_out.
    #
    # Now, the excess that we couldn't assign has to go somewhere: (1) to the
    # other output belt; if that's full, (2) feed back up the chain by reducing
    # input velocities.
    excess_from_1 = s.Max(s.Real(0), s.Minus(half_input, belts[y1][out].v))
    excess_from_2 = s.Max(s.Real(0), s.Minus(half_input, belts[y2][out].v))

    # This formula is most accurate for assignment > velocity (density will
    # equal 1), but it doesn't change the flux calculation just toset rho to
    # the velocity when velocity limits flow. (So you should be able to replace
    # the Ite by v_out and be OK.)
    formula.append(
        s.Equals(
            belts[y1][out].rho,
            s.Ite(half_input + excess_from_2 > belts[y1][out].v, s.Real(1),
                  half_input + excess_from_2)))
    formula.append(
        s.Equals(
            belts[y2][out].rho,
            s.Ite(half_input + excess_from_1 > belts[y2][out].v, s.Real(1),
                  half_input + excess_from_1)))

    output_v = s.Plus(belts[y1][out].v, belts[y2][out].v)
    half_output = s.Div(output_v, s.Real(2))
    unused_density_from_1 = s.Max(s.Real(0),
                                  s.Minus(half_output, belts[y1][inn].rho))
    unused_density_from_2 = s.Max(s.Real(0),
                                  s.Minus(half_output, belts[y2][inn].rho))

    formula.append(
        s.Equals(
            belts[y1][inn].v,
            s.Ite(half_output + unused_density_from_2 > belts[y1][inn].rho,
                  s.Real(1), half_output + unused_density_from_2)))
    formula.append(
        s.Equals(
            belts[y2][inn].v,
            s.Ite(half_output + unused_density_from_1 > belts[y2][inn].rho,
                  s.Real(1), half_output + unused_density_from_1)))
    # Conservation of flux at each junction.
    input_flux = s.Plus(belts[y1][inn].flux, belts[y2][inn].flux)
    output_flux = s.Plus(belts[y1][out].flux, belts[y2][out].flux)
    formula.append(s.Equals(input_flux, output_flux))

  # Any belts not involved in a junction are pass-throughs. Their successive
  # values must remain equal.
  thru_belts = [
      list(
          set(range(width)) - {y1 for y1, y2 in junctions_by_x[x]} -
          {y2 for y1, y2 in junctions_by_x[x]}) for x in range(length + 1)
  ]
  for x, thru in enumerate(thru_belts[1:]):
    for y in thru:
      formula.append(s.Equals(belts[y][x].rho, belts[y][x + 1].rho))
      formula.append(s.Equals(belts[y][x].v, belts[y][x + 1].v))

  return formula, belts


def check_balancer_flow(junctions, upstream_densities, downstream_velocities):
  assert len(upstream_densities) == len(downstream_velocities)
  width = len(upstream_densities)
  length = max(x for x, _, _ in junctions)

  formula, belts = balancer_flow_formula(junctions, width, length)

  # Set initial conditions.
  for y, rho in enumerate(upstream_densities):
    formula.append(s.Equals(belts[y][0].rho, s.Real(rho)))
  for y, v in enumerate(downstream_velocities):
    formula.append(s.Equals(belts[y][-1].v, s.Real(v)))

  m = get_model_or_print_ucore(s.And(formula))
  # Print output diagram.
  junctions_by_x = [[] for x in range(length + 1)]
  for (x, y1, y2) in junctions:
    junctions_by_x[x].append((y1, y2))
  for y, beltway in enumerate(belts):
    print(f'{upstream_densities[y]}>>>', end=':')
    for x, belt in enumerate(beltway):

      letter_map = {}
      if x < len(beltway) - 1:
        for (y1, y2), letter in zip(junctions_by_x[x + 1], 'abcdefghjkmn'):
          assert y1 not in letter_map
          assert y2 not in letter_map
          letter_map[y1] = letter
          letter_map[y2] = letter

      print(f' >>>{m.get_value(belt.rho)}@{m.get_value(belt.v)}>>>',
            end=f' {letter_map.get(y,"|")}')
    end_flux = m.get_py_value(beltway[-1].flux)
    print(f'> {end_flux}.')

  # The moment of truth...
  theoretical_throughput = min(sum(upstream_densities),
                               sum(downstream_velocities))
  print(f'Theoretical Q: {theoretical_throughput}')
  actual_throughput = sum(m.get_py_value(beltway[-1].flux) for beltway in belts)
  print(f'Actual Q: {actual_throughput}')
  if theoretical_throughput != actual_throughput:
    print(
        f'{float(1-(actual_throughput/theoretical_throughput)):.0%} slowdown :('
    )
  print('∎')


def prove_utu(junctions):
  width = max(max(y1 for _, y1, _ in junctions),
              max(y2 for _, _, y2 in junctions)) + 1
  length = max(x for x, _, _ in junctions)
  formula, belts = balancer_flow_formula(junctions, width, length)

  supply = s.Plus(beltway[0].rho for beltway in belts)
  demand = s.Plus(beltway[-1].v for beltway in belts)
  max_theoretical_throughput = s.Min(supply, demand)
  actual_throughput = s.Plus(beltway[-1].flux for beltway in belts)
  ## counter_example_formula = s.And(
  ##     s.And(formula),
  ##     s.Or(s.Not(s.Equals(beltway[-1].flux)), s.Not(s.Equals(max_theoretical_throughput, actual_throughput))))
  counter_example_formula = s.And(
      s.And(formula),
      s.Not(s.Equals(max_theoretical_throughput, actual_throughput)))
  m = s.get_model(counter_example_formula)
  if not m:
    print("It's UTU!")
    return
  inputs = tuple(m.get_py_value(beltway[0].rho) for beltway in belts)
  outputs = tuple(m.get_py_value(beltway[-1].v) for beltway in belts)
  print(f'Input lane densities: ({", ".join(map(str, inputs))})')
  print(f'Output lane velocities: ({", ".join(map(str, outputs))})')
  check_balancer_flow(junctions, inputs, outputs)


examples = [
    (
        #1
        [(1, 0, 1)],
        (1, 0),
        (1, 1),
    ),
    (
        #2
        [(1, 0, 1), (2, 1, 2)],
        (1, 0, 1),
        (1, 1, 1),
    ),
    (
        #3
        [(1, 0, 1)],
        (1, 0),
        (0, 1),
    ),
    (
        #4
        [(1, 0, 1)],
        (0.5, 0.75),
        (0, 1),
    ),
    (
        #5
        [(1, 0, 1), (2, 1, 2)],
        (1, 0, 0),
        (0, 0, 1),
    ),
    (
        #6
        [
            (1, 0, 1),
        ],
        (1, 0, 0),
        (0, 0, 1)),
    (
        #7
        [(1, 0, 1), (2, 1, 2), (3, 0, 1)],
        (1, 1, 1),
        (1, 0, 1)),
    (
        #8
        [(1, 0, 1), (2, 1, 2), (3, 0, 1), (4, 1, 2), (5, 0, 1)],
        (1, 1, 0),
        (1, 1, 1)),
    (
        #9 - non-UTU
        [(1, 0, 1), (2, 1, 2), (3, 0, 1), (4, 1, 2)],
        (1, 1, 0),
        (0, 1, 1)),
    (
        #10 - smallest UTU 4-belt.
        [
            (1, 0, 1),
            (1, 2, 3),
            (2, 1, 2),
            (2, 0, 3),
            (3, 0, 1),
            (3, 2, 3),
        ],
        (1, 1, 1, 0),
        (1, 1, 0, 1),
    ),
    (
        #11 - example that does not converge (quickly) with an iterative method
        #(In[26] in original notebook).
        [
            (1, 0, 1),
            (2, 1, 2),
            (3, 2, 3),
            (4, 1, 2),
            (5, 0, 1),
            (6, 1, 2),
            (7, 2, 3),
            (8, 1, 2),
            (9, 0, 1),
        ],
        (1, 1, 1, 0),
        (0, 1, 1, 1),
    ),
    (
      #12 - claims to be the smallest 5-belt UTU
        [
            (1, 0, 1),
            (1, 2, 3),
            (2, 1, 2),
            (2, 3, 4),
            (3, 4, 0),
            (3, 2, 3),
            (4, 0, 1),
            (4, 2, 3),
            (5, 1, 2),
            (5, 3, 4),
            (6, 4, 0),
            (6, 2, 3),
            (7, 0, 1),
            (7, 2, 3),
            (8, 1, 2),
            (8, 3, 4),
            (9, 4, 0),
            (9, 2, 3),
        ],
        (1, 0, 1, 0, 1),
        (0, 1, 0, 1, 0),
    ),
]

if __name__ == '__main__':
  for i, example in enumerate(examples[9:10]):
    junctions, upstream_densities, downstream_velocities = example
    header = f'Example {i+1}'
    print(header)
    print('=' * len(header))
    #check_balancer_flow(junctions, upstream_densities, downstream_velocities)
    prove_utu(junctions)
