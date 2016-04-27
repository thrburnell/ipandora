const path = require('path');

const PATHS = {
  app: {
    js: path.join(__dirname, 'app/js'),
    css: path.join(__dirname, 'app/css')
  },
  build: path.join(__dirname, 'dist')
};

module.exports = {
  entry: {
    app: PATHS.app.js
  },
  output: {
    path: PATHS.build,
    filename: 'main.js'
  },
  module: {
    loaders: [
      {
        test: /\.css$/,
        loaders: ['style', 'css'],
        include: PATHS.app.css
      }
    ]
  }
};

