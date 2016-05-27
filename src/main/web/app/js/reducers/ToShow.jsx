import { RECEIVE_INDUCTION_SCHEMA } from '../actions'

const ToShow = (state={}, action) => {
  
  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return {
        formula: action.toShow,
        valid: true
      }
    default:
      return state
  }
}

export default ToShow

