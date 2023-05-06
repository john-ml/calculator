import flask as F
from flask import Flask

class Prog:
  def __init__(self):
    self.state = []

  def on_input(self, cmds):
    def go(stack, cmds):
      match stack, cmds:
        case stack, []:
          self.state = stack
          return stack
        case [*stack, v, w], ['+', *cmds]: return go([*stack, v + w], cmds)
        case [*stack, v, w], ['*', *cmds]: return go([*stack, v * w], cmds)
        case stack, [c, *cmds]: return go([*stack, float(c)], cmds)
    return str(go(self.state, cmds))

  def tex(self, s):
    return f'{s}'

def base64image(path):
  import base64
  with open(path, 'rb') as f:
    bytes = f.read()
  return base64.b64encode(bytes).decode('utf-8')

def img(path):
  return f'<img src="data:image/png;base64,{base64image(path)}"></img>'

app = Flask(__name__)   
prog = Prog()

@app.route('/', methods = ['GET'])
def main():
  return F.render_template('index.html')

@app.route('/input', methods = ['POST'])
def on_input():
  from html import unescape
  s = unescape(F.request.data.decode('utf-8'))
  if s.endswith('<br>'): s = s[:-len('<br>')]
  print('Received input:', s)
  try: return prog.on_input(s.split())
  # try: return prog.tex(s)
  except: return img('lfman.png')

if __name__ == '__main__':
  app.run()