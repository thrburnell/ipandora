import { combineReducers } from 'redux'
import {reducer as formReducer} from 'redux-form';
import { SAVE_GIVEN_INDEX } from '../actions'
import mode from './Mode'
import toShow from './ToShow'
import proof from './Proof'
import given from './Given'

const ipandoraApp = combineReducers({
  mode,
  toShow,
  proof,
  given,
  form: formReducer
})

export default ipandoraApp

