import React from 'react'

const TakeArbitraryLine = ({
  fields: { name, domain },
  onSubmit,
  handleSubmit,
  submitting,
  onCloseClick
}) => {

  const nameClassName = ["col-sm-6",
    name.touched && name.error ? "has-error" : ""].join(" ")

  const domainClassName = ["col-sm-3",
    domain.touched && domain.error ? "has-error" : ""].join(" ")

  return (
    <form className="form-horizontal" onSubmit={ handleSubmit }>
      <div className="form-group bottom-no-margin">
        <div className={ nameClassName }>
          <input type="text" {...name}
           className="form-control monospace-font" placeholder="..." />
        </div>
        <div className={ domainClassName }>
          <select className="form-control full-width" {...domain}>
            <option></option>
            <option value="Unknown">Universe</option>
            <option value="Nat">Nat</option>
          </select>
        </div>
        <div className="col-sm-2 text-right">
          <button type="submit" className="btn btn-primary full-width"
           disabled={ submitting }>Add</button>
        </div>
        <div className="col-sm-1 text-right">
          <button type="button" className="btn btn-default full-width"
           onClick={ onCloseClick }>
            x
          </button>
        </div>
      </div>
    </form>
  )
}

export default TakeArbitraryLine

