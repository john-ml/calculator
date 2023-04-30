import flask as F
from flask import Flask

def base64image(path):
  import base64
  with open(path, 'rb') as f:
    bytes = f.read()
  return base64.b64encode(bytes).decode('utf-8')

def img(path):
  return f'<img src="data:image/png;base64,{base64image(path)}"></img>'

app = Flask(__name__)   

@app.route('/', methods = ['GET'])
def main():
  return F.render_template('index.html')

@app.route('/input', methods = ['POST'])
def on_input():
  from html import unescape
  s = unescape(F.request.data.decode('utf-8'))
  if s.endswith('<br>'): s = s[:-len('<br>')]
  print('Received input:', s)
  try:
    def go(stack, cmds):
      print(stack, cmds)
      match stack, cmds:
        case [h, *_], []: return h
        case [v, w, *stack], ['+', *cmds]: return go([v + w, *stack], cmds)
        case [v, w, *stack], ['*', *cmds]: return go([v * w, *stack], cmds)
        case stack, [c, *cmds]: return go([float(c), *stack], cmds)
    return str(go([], s.split()))
  except:
    return img('lfman.png')

if __name__ == '__main__':
  app.run()