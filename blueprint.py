import base64
import zlib
import sys
import pprint
import json

def decode(s):
  if s[0] != '0':
    raise Exception('Unsupported blueprint version')
  return json.loads(zlib.decompress(base64.b64decode(s[1:])).decode())
def encode(j):
  s = json.dumps(j)
  z = zlib.compress(s.encode(), level=9)
  b = base64.b64encode(z)
  return b'0' + b

if __name__ == '__main__':
  if '-d' in sys.argv:
    pprint.pprint(decode(sys.stdin.read()))
  else:
    sys.stdout.write(encode(json.loads(sys.stdin.read())))
