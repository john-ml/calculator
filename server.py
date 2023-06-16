import flask as FL
from flask import Flask

# ----------

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
  return FL.render_template('index.html')

@app.route('/input', methods = ['POST'])
def on_input():
  import html as H
  s = H.unescape(FL.request.data.decode('utf-8'))
  if s.endswith('<br>'): s = s[:-len('<br>')]
  print('Received input:', s)
  try:
    return f'${s}$'
  except Exception as e:
    return H.escape(str(e)).replace('\n', '<br>')

if __name__ == '__main__':
  app.run()