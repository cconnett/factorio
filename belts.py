import dataclasses
import fractions
import pysmt.shortcuts as s
import pysmt.typing as t

s.get_env().enable_infix_notation = True


@dataclasses.dataclass
class Belt:
  rho: t.REAL
  v: t.REAL

  @property
  def flux(self):
    return s.Min(self.rho, self.v)


def domain(belt):
  yield 0 <= belt.rho <= 1
  yield 0 <= belt.v <= 1
  # yield s.LT(belt.rho, s.Real(1)).Implies(s.Equals(belt.v, s.Real(1)))
  # yield s.LT(belt.v, s.Real(1)).Implies(s.Equals(belt.rho, s.Real(1)))


def balancer_flow(junctions, upstream_densities, downstream_velocities):
  upstream_densities = [fractions.Fraction(d) for d in upstream_densities]
  downstream_velocities = [fractions.Fraction(v) for v in downstream_velocities]
  n = len(upstream_densities)
  length = max(x for x, _, _ in junctions)
  assert n == len(downstream_velocities)

  formula = []
  belts = [[
      Belt(s.Symbol(f'b{i}[{x}].rho', t.REAL), s.Symbol(f'b{i}[{x}].v', t.REAL))
      for x in range(length + 1)
  ]
           for i in range(n)]
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
    # the velocity when velocity limits flow. (So you could replace the Ite by
    # v_out and be OK.)
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
    empty_demand_of_1 = s.Max(s.Real(0), s.Minus(half_output,
                                                 belts[y1][inn].rho))
    empty_demand_of_2 = s.Max(s.Real(0), s.Minus(half_output,
                                                 belts[y2][inn].rho))

    formula.append(
        s.Equals(
            belts[y1][inn].v,
            s.Ite(half_output + empty_demand_of_2 > belts[y1][inn].rho,
                  s.Real(1), half_output + empty_demand_of_2)))
    formula.append(
        s.Equals(
            belts[y2][inn].v,
            s.Ite(half_output + empty_demand_of_1 > belts[y2][inn].rho,
                  s.Real(1), half_output + empty_demand_of_1)))
    # Conservation of flux at each junction.
    input_flux = s.Plus(belts[y1][inn].flux, belts[y2][inn].flux)
    output_flux = s.Plus(belts[y1][out].flux, belts[y2][out].flux)
    formula.append(s.Equals(input_flux, output_flux))

  # Any belts not involved in a junction are pass-throughs. Their successive
  # values must remain equal.
  thru_belts = [
      list(
          set(range(n)) - {y1 for y1, y2 in junctions_by_x[x]} -
          {y2 for y1, y2 in junctions_by_x[x]}) for x in range(length + 1)
  ]
  for x, thru in enumerate(thru_belts[1:]):
    for y in thru:
      formula.append(s.Equals(belts[y][x].rho, belts[y][x + 1].rho))
      formula.append(s.Equals(belts[y][x].v, belts[y][x + 1].v))

  # Set initial conditions.
  for y, rho in enumerate(upstream_densities):
    formula.append(s.Equals(belts[y][0].rho, s.Real(rho)))
  for y, v in enumerate(downstream_velocities):
    formula.append(s.Equals(belts[y][length].v, s.Real(v)))

  # Crunch time!
  m = s.get_model(s.And(formula))
  if not m:
    print('unsat')
    from pysmt.rewritings import conjunctive_partition
    conj = conjunctive_partition(s.And(formula))
    ucore = s.get_unsat_core(conj)
    print("UNSAT-Core size '%d'" % len(ucore))
    for f in ucore:
      print(f.serialize())

    return

  # Print output diagram.
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
    print(f'{float(1-(actual_throughput/theoretical_throughput)):.0%} slowdown :(')
  print('∎')


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
        (1, 1, 0)),
    (
        #8a - non-UTU
        [(1, 0, 1), (2, 1, 2), (3, 0, 1), (4, 1, 2)],
        (1, 1, 0),
        (0, 1, 1)),
]

if __name__ == '__main__':
  for i, example in enumerate(examples):
    header = f'Example {i+1}'
    print(header)
    print('=' * len(header))
    balancer_flow(*example)
