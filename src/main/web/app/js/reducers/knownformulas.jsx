const knownFormulas = (state = {}, action) => {

  switch (action.type) {
    case 'ADD_GIVEN':
      return {
        ...state,
        [action.id]: {
          id: action.id,
          uiId: action.uiId,
          formula: action.formula
        }
      }
    
    case 'RECEIVE_CHECK_STATUS':
      if (action.valid) {
        return {
          ...state,
          [action.id]: {
            id: action.id,
            uiId: action.uiId,
            formula: action.formula
          }
        }
      }

      return state

    default:
      return state
  }

}

export default knownFormulas

