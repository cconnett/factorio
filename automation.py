import z3
import blueprint
import dataclasses


def blueprint_json(model):
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
        'entity_number': i + 1,
        'name': m.entity_name,
        'position': {
            'x': int(str(model[m.x])) - WIDTH / 2 + m.width / 2 - 0.5,
            'y': int(str(model[m.y])) - HEIGHT / 2 + m.height / 2 - 0.5
        }
    })
  return template


s = z3.Solver()

WIDTH = 10
HEIGHT = 10


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

machines = assemblers + power
for i in machines:
  for j in machines:
    if i != j:
      s.add(
          z3.Or(i.x - j.x >= j.width, i.x - j.x <= -i.width,
                i.y - j.y >= j.height, i.y - j.y <= -i.height))

for a in assemblers:
  s.add(
      z3.Or([z3.And(p.x - (a.x + a.width - 1) <= 3, a.x - p.x <= 3)
            for p in power]))
  s.add(
      z3.Or([z3.And(p.y - (a.y + a.height - 1) <= 3, a.y - p.y <= 3)
            for p in power]))
print('check')
if s.check() == z3.sat:
  print(s.model())
  print(blueprint.encode(blueprint_json(s.model())).decode())
else:
  print('unsat')
