import expose from 'expose?$!expose?jQuery!jQuery'
import bootstrap from 'bootstrap-webpack'
import '../css/main.css'

import React from 'react'
import { render } from 'react-dom'
import { Provider } from 'react-redux'
import { createStore, applyMiddleware } from 'redux'
import thunkMiddleware from 'redux-thunk'
import ipandoraApp from './reducers'
import App from './components/App'

const initialState = {
  toShow: { valid: true }
}

let store = createStore(
  ipandoraApp,
  initialState,
  applyMiddleware(thunkMiddleware)
)

render(
  <Provider store={store}>
    <App />
  </Provider>,
  document.getElementById('app')
)

