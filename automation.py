import z3
import blueprint
import dataclasses
import itertools
from typing import List


def blueprint_json(model):
  entity_number = itertools.count(1)
  template = {
      'blueprint': {
          'entities': [],
          'icons': [{
              'index': 1,
              'signal': {
                  'name': 'automation-science-pack',
                  'type': 'item'
              }
          }],
          'item': 'blueprint',
          'label': 'Blueprint',
          'version': 281479272333311
      }
  }
  entities = template['blueprint']['entities']
  for i, m in enumerate(machines):
    entities.append({
        'entity_number': next(entity_number),
        'name': m.entity_name,
        'position': {
            'x': model[m.x].as_long() - WIDTH / 2 + m.width / 2 - 0.5,
            'y': model[m.y].as_long() - HEIGHT / 2 + m.height / 2 - 0.5
        }
    })
  for x in range(-1, WIDTH):
    for y in range(HEIGHT):
      if (s := model.eval(structure(x, y))) in (BELT, INSERTER):
        entities.append({
            'entity_number': next(entity_number),
            'name': 'express-transport-belt' if s == BELT else 'fast-inserter',
            'position': {
                'x': x - WIDTH / 2,
                'y': y - HEIGHT / 2
            },
            'direction': dir_to_factorio[model.eval(direction(x, y))]
        })

  return template

def print_resources(m):
  resource_glyphs = {COPPER: 'C', IRON: 'I', COG: '*', NO_RESOURCE: ' ', RED_SCIENCE: 'R'}
  for x in range(WIDTH):
    for y in range(HEIGHT):
      print(resource_glyphs[m.eval(resource(x,y))], end='')
    print()

s = z3.Solver()
(DirectionSort, (
    UP,
    RIGHT,
    DOWN,
    LEFT,
)) = z3.EnumSort('Direction', ['UP', 'RIGHT', 'DOWN', 'LEFT'])
(ResourceSort, (
    NO_RESOURCE,
    COPPER,
    IRON,
    COG,
    RED_SCIENCE,
)) = z3.EnumSort('Resource', [
    'NO_RESOURCE',
    'COPPER',
    'IRON',
    'COG',
    'RED_SCIENCE',
])
(
    StructureSort,
    (
        NO_STRUCTURE,
        BELT,
        INSERTER,
        #LONG_INSERTER,
        OTHER_STRUCTURE,
    )) = z3.EnumSort(
        'Object',
        [
            'NO_STRUCTURE',
            'BELT',
            'INSERTER',
            #'LONG_INSERTER',
            'OTHER_STRUCTURE',
        ])

WIDTH = 10
HEIGHT = 10

dir_to_factorio = {UP: 0, RIGHT: 2, DOWN: 4, LEFT: 6}
resource = z3.Function('resource', z3.IntSort(), z3.IntSort(), ResourceSort)
structure = z3.Function('structure', z3.IntSort(), z3.IntSort(), StructureSort)
direction = z3.Function('direction', z3.IntSort(), z3.IntSort(), DirectionSort)
is_input = z3.Function('is_input', z3.IntSort(), z3.IntSort(), z3.BoolSort())
machine_output = z3.Function('machine_output', z3.IntSort(), z3.IntSort(),
                             ResourceSort)


@dataclasses.dataclass
class Recipe:
  recipe_name: str
  input_resources: List[type(NO_RESOURCE)]
  output_resource: List[type(NO_RESOURCE)]


class Machine:
  entity_name: str
  machine_id: int
  x: z3.ArithRef
  y: z3.ArithRef
  width: int
  height: int
  recipe: Recipe

  def __init__(self, entity_name, machine_id, width, height, recipe=None):
    self.entity_name = entity_name
    self.machine_id = machine_id
    self.width = width
    self.height = height
    self.recipe = recipe
    self.x = z3.Int(f'{self.entity_name}-{self.machine_id}.x')
    self.y = z3.Int(f'{self.entity_name}-{self.machine_id}.y')

  def AddToSolver(self, s):
    s.add(self.x >= 0)
    s.add(self.y >= 0)
    s.add(self.x < WIDTH - self.width)
    s.add(self.y < HEIGHT - self.height)


RedScience = Recipe('automation-science-pack', [COG, COPPER], RED_SCIENCE)
IronGearWheel = Recipe('iron-gear-wheel', [IRON], COG)

assemblers = [
    Machine('assembling-machine-3', n + 1, 3, 3, RedScience) for n in range(4)
]
assemblers.append(Machine('assembling-machine-3', 5, 3, 3, IronGearWheel))
power = [Machine('medium-electric-pole', n + 1, 1, 1) for n in range(1)]
for a in assemblers:
  a.AddToSolver(s)

for p in power:
  p.AddToSolver(s)

# These are opposite of what the coordinates suggest. This is because we use
# the direction value to determine what direction *the neighbor* should have to
# feed its resource *into* this cell.
directional_offsets = [
    (DOWN, (0, -1)),
    (LEFT, (1, 0)),
    (UP, (0, 1)),
    (RIGHT, (-1, 0)),
]
opposite_direction = {UP: DOWN, RIGHT: LEFT, DOWN: UP, LEFT: RIGHT}
# Apply resource transfer rules.
for x in range(WIDTH):
  for y in range(HEIGHT):
    s.add(z3.Implies(structure(x,y) == INSERTER, resource(x,y) == NO_RESOURCE))
    # `or` together necessary and sufficient conditions for a coordinate to
    # have a resource. The first such condition, `is_input`, is how we bless
    # certain squares as being able to have resources from nothing. It could
    # always be empty, too.
    cases = [is_input(x, y), resource(x, y) == NO_RESOURCE]
    # Because these are functions, not fixed arrays, we can reference
    # out-of-bounds locations without issue.
    for neighbor_direction, (x_offset, y_offset) in directional_offsets:
      # Fed by a belt on this neighbor,
      cases.append(
          z3.And(
              resource(x, y) == resource(x + x_offset, y + y_offset),
              structure(x + x_offset, y + y_offset) == BELT,
              direction(x + x_offset, y + y_offset) == neighbor_direction,
            direction(x, y) != opposite_direction[neighbor_direction]))
      # or fed by an inserter on this neighbor.
      cases.append(
          z3.And(
              resource(x, y) == resource(x + 2 * x_offset, y + 2 * y_offset),
              structure(x + x_offset, y + y_offset) == INSERTER,
              direction(x + x_offset, y + y_offset) == neighbor_direction))
    s.add(z3.Or(cases))

s.add(resource(-1, 5) == COPPER)
s.add(structure(-1, 5) == BELT)
s.add(direction(-1, 5) == RIGHT)
s.add(is_input(-1, 5))

s.add(resource(-1, 6) == IRON)
s.add(structure(-1, 6) == BELT)
s.add(direction(-1, 6) == RIGHT)
s.add(is_input(-1, 6))

for x in range(-2, WIDTH + 2):
  for y in range(-2, HEIGHT + 2):
    if not 0 <= x < WIDTH or not 0 <= y < HEIGHT:
      if (x, y) not in [(-1, 5), (-1, 6)]:
        s.add(resource(x, y) == NO_RESOURCE)
        s.add(structure(x, y) == NO_STRUCTURE)
        s.add(z3.Not(is_input(x, y)))
    else:
      s.add(z3.Not(is_input(x, y)))

machines = assemblers + power
for i in machines:
  s.add(
      z3.And([
          structure(i.x + x, i.y + y) == OTHER_STRUCTURE
          for x in range(i.width)
          for y in range(i.height)
      ]))

  for j in machines:
    if i != j:
      s.add(
          z3.Or(i.x - j.x >= j.width, i.x - j.x <= -i.width,
                i.y - j.y >= j.height, i.y - j.y <= -i.height))

for a in assemblers:
  s.add(
      z3.Or([
          z3.And(p.x - (a.x + a.width - 1) <= 3, a.x - p.x <= 3) for p in power
      ]))
  s.add(
      z3.Or([
          z3.And(p.y - (a.y + a.height - 1) <= 3, a.y - p.y <= 3) for p in power
      ]))

print('check')
if s.check() == z3.sat:
  m = s.model()
  print(m)
  print_resources(m)
  # import pdb; pdb.set_trace()
  print(blueprint.encode(blueprint_json(m)).decode())
else:
  print('unsat')
