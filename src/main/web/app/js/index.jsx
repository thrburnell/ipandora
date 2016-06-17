import expose from 'expose?$!expose?jQuery!jQuery'
import bootstrap from 'bootstrap-webpack'
import '../css/main.css'

import React from 'react'
import { render } from 'react-dom'
import { Provider } from 'react-redux'
import { createStore, applyMiddleware } from 'redux'
import thunkMiddleware from 'redux-thunk'
import ipandoraApp from './reducers'
import RApp from './containers/RApp'

let store = createStore(
  ipandoraApp,
  applyMiddleware(thunkMiddleware)
)

render(
  <Provider store={store}>
    <RApp />
  </Provider>,
  document.getElementById('app')
)

