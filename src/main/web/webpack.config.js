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
  resolve: {
    extensions: ['', '.js', '.jsx']
  },
  output: {
    path: PATHS.build,
    filename: 'main.js'
  },
  module: {
    loaders: [
     {
        // Accepts js and jsx
        test: /\.jsx?$/,
        // Enable caching
        loaders: ['babel?cacheDirectory'],
        include: PATHS.app.js
      },
      {
        test: /\.css$/,
        loaders: ['style', 'css']
        // include: [ PATHS.app.css, 'node_modules/bootstrap/dist/css' ]
      },
      {
        test: /\.eot(\?v=\d+\.\d+\.\d+)?$/, 
        loader: 'file'
      },
      {
        test: /\.(woff|woff2)$/,
        loader: 'url?prefix=font/&limit=5000'
      },
      {
        test: /\.ttf(\?v=\d+\.\d+\.\d+)?$/,
        loader: 'url?limit=10000&mimetype=application/octet-stream'
      },
      {
        test: /\.svg(\?v=\d+\.\d+\.\d+)?$/,
        loader: 'url?limit=10000&mimetype=image/svg+xml'
      }
    ]
  },
  plugins: [
    new CopyWebpackPlugin([{ from: 'app/index.html' }])
  ]
};

