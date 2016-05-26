import 'bootstrap/dist/css/bootstrap.css'
import '../css/main.css'

import React from 'react'
import { render } from 'react-dom'
import { Provider } from 'react-redux'
import { createStore, applyMiddleware } from 'redux'
import thunkMiddleware from 'redux-thunk'
import ipandoraApp from './reducers'
import App from './components/App'

const initialState = {
  toShow: "Default to show",
  baseCase: {
    active: false
  },
  inductiveCase: {
    active: false
  }
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

