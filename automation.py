import z3
import blueprint
import dataclasses
import itertools


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
  for x in range(WIDTH):
    for y in range(HEIGHT):
      if model.eval(belt(x, y)):
        entities.append({
            'entity_number': next(entity_number),
            'name': 'express-transport-belt',
            'position': {
                'x': x - WIDTH / 2,
                'y': y - HEIGHT / 2
            },
            'direction': dir_to_factorio[model.eval(direction(x, y))]
        })

  return template


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
)) = z3.EnumSort('Resource', ['NO_RESOURCE', 'COPPER', 'IRON'])

WIDTH = 10
HEIGHT = 10

dir_to_factorio = {UP: 0, RIGHT: 2, DOWN: 4, LEFT: 6}
copper = z3.Function('copper', z3.IntSort(), z3.IntSort(), z3.BoolSort())
iron = z3.Function('iron', z3.IntSort(), z3.IntSort(), z3.BoolSort())
belt = z3.Function('belt', z3.IntSort(), z3.IntSort(), z3.BoolSort())
direction = z3.Function('direction', z3.IntSort(), z3.IntSort(), DirectionSort)

s.add(copper(0, 5))


class Machine:
  entity_name: str
  machine_id: int
  x: z3.ArithRef
  y: z3.ArithRef
  width: int
  height: int

  def __init__(self, entity_name, machine_id, width, height):
    self.entity_name = entity_name
    self.machine_id = machine_id
    self.width = width
    self.height = height
    self.x = z3.Int(f'{self.entity_name}-{self.machine_id}.x')
    self.y = z3.Int(f'{self.entity_name}-{self.machine_id}.y')

  def AddToSolver(self, s):
    s.add(self.x >= 0)
    s.add(self.y >= 0)
    s.add(self.x < WIDTH - self.width)
    s.add(self.y < HEIGHT - self.height)


assemblers = [Machine('assembling-machine-3', n + 1, 3, 3) for n in range(5)]
power = [Machine('medium-electric-pole', n + 1, 1, 1) for n in range(1)]
for a in assemblers:
  a.AddToSolver(s)

for p in power:
  p.AddToSolver(s)

for x in range(WIDTH):
  for y in range(HEIGHT):
    cases = []
    if x > 0:
      cases.append(
          z3.And(copper(x - 1, y), belt(x - 1, y),
                 direction(x - 1, y) == RIGHT))
    if x < WIDTH - 1:
      cases.append(
          z3.And(copper(x + 1, y), belt(x + 1, y),
                 direction(x + 1, y) == LEFT))
    if y > 0:
      cases.append(
          z3.And(copper(x, y - 1), belt(x, y - 1),
                 direction(x, y - 1) == DOWN))
    if y > HEIGHT - 1:
      cases.append(
          z3.And(copper(x, y + 1), belt(x, y + 1),
                 direction(x, y + 1) == UP))
    s.add(copper(x, y) == z3.Or(cases))

machines = assemblers + power
for i in machines:
  s.add(
      z3.And([
          z3.Not(belt(i.x + x, i.y + y))
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
  print(s.model())
  print(blueprint.encode(blueprint_json(s.model())).decode())
else:
  print('unsat')
