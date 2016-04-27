const path = require('path');
const CopyWebpackPlugin = require('copy-webpack-plugin');

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
  },
  plugins: [
    new CopyWebpackPlugin([{ from: 'app/index.html' }])
  ]
};

