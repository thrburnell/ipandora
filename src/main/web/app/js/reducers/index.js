import { combineReducers } from 'redux'
import givens from './givens'
import toShows from './toshows'

const ipandoraApp = combineReducers({
  givens,
  toShows
})

export default ipandoraApp

