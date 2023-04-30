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
    print(F.request.data)
    # return 'Your key is ' + request.data.decode('utf-8') + ' and here is a bunch more data'
    return img('tmp/lfman.png')

if __name__ == '__main__':
   app.run()