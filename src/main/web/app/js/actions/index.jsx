import fetch from 'isomorphic-fetch'

export const RECEIVE_FUNCTION_VALIDITY = 'RECEIVE_FUNCTION_VALIDITY'
export const RECEIVE_INDUCTION_SCHEMA = 'RECEIVE_INDUCTION_SCHEMA'
export const SAVE_BASE_INITIAL_TERM = 'SAVE_BASE_INITIAL_TERM'
export const RECEIVE_BASE_PROOF_STEP_VALIDITY = 'RECEIVE_BASE_PROOF_STEP_VALIDITY'

export const validateFunction = (fn) => {
  return (dispatch, getState) => {

    const request = new Request('/api/predicate/function', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        function: fn
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveFunctionValidity(fn, json.prototype, json.valid))
      })
      .catch(err => console.log(err))
  }
}

export const receiveFunctionValidity = (fn, prototype, valid) => (
  {
    type: RECEIVE_FUNCTION_VALIDITY,
    fn,
    prototype,
    valid
  }
)

export const getInductionSchema = (formula, variable) => {
  return (dispatch, getState) => {
  
    const request = new Request('/api/predicate/induction', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        goal: formula,
        variable
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveInductionSchema(json.goal, json.baseCase, json.inductiveCase))
      })
      .catch(err => console.log(err))
  }
}

export const receiveInductionSchema = (toShow, baseCase, inductiveCase) => (
  {
    type: RECEIVE_INDUCTION_SCHEMA,
    toShow,
    baseCase,
    inductiveCase
  }
)

export const saveBaseInitialTerm = (term) => (
  {
    type: SAVE_BASE_INITIAL_TERM,
    term
  }
)

export const makeBaseProofStep = (term, justification) => {
  return (dispatch, getState) => {

    const steps = getState().baseCase.steps
    const latest = steps[steps.length-1].term
    
    const body = {
      method: justification,
      goal: term,
      from: latest
    }

    if (justification == 'FUNCTION_DEFINITION') {
      body.function = getState().fn.definition
      body.functions = getState().prototypes
    }

    const request = new Request('/api/predicate/step', {
      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify(body)
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        dispatch(receiveBaseProofStepValidity(term, justification, json.valid))
      })
      .catch(err => console.log(err))
  }
}

export const receiveBaseProofStepValidity = (term, justification, valid) => (
  {
    type: RECEIVE_BASE_PROOF_STEP_VALIDITY,
    term,
    justification,
    valid
  }
)


