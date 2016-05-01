import 'bootstrap/dist/css/bootstrap.css'
import '../css/main.css'

import React from 'react'
import { render } from 'react-dom'
import { Provider } from 'react-redux'
import { createStore } from 'redux'
import ipandoraApp from './reducers'
import App from './components/App'

let store = createStore(ipandoraApp)

render(
  <Provider store={store}>
    <App />
  </Provider>,
  document.getElementById('app')
)

