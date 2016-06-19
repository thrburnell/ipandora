import { RECEIVE_TO_SHOW_VALIDATION } from '../actions'

const ToShow = (state={}, action) => {
  
  switch (action.type) {
    case RECEIVE_TO_SHOW_VALIDATION:
      return {
        formula: action.formula,
        valid: action.valid
      }

    default:
      return state
  }
}

export default ToShow

