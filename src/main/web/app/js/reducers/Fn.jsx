import { RECEIVE_FUNCTION_VALIDITY } from '../actions'

const Fn = (state={}, action) => {

  switch (action.type) {
    case RECEIVE_FUNCTION_VALIDITY:
      return {
        definition: action.fn,
        valid: action.valid
      }
    default:
      return state
  }
}

export default Fn

